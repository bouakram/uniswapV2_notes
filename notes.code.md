# Code Notes

## contract => v2-periphery_UniswapV2Router02.sol

### function Swap

```javascript
// fetches and sorts the reserves for a pair
function getReserves(address factory, address tokenA, address tokenB) internal view returns (uint reserveA, uint reserveB) {
    // (@dai) = sortTokens(@eth, @dai)
    (address token0,) = sortTokens(tokenA, tokenB);
    /*
    for this e.g this function is called from the @eth/@dai pair
    function getReserves() public view returns (uint112 _reserve0, uint112 _reserve1, uint32 _blockTimestampLast) {
        _reserve0 = reserve0; // dai reserve
        _reserve1 = reserve1; // eth reserve
        _blockTimestampLast = blockTimestampLast;
    }
    */
    // (1000 eth, 1,000,000 dai) = IUniswapV2Pair(pairFor(factory, @eth, @dai)).getReserves();
    (uint reserve0, uint reserve1,) = IUniswapV2Pair(pairFor(factory, tokenA, tokenB)).getReserves();
    // (reserveA, reserveB) = @eth == @dai ? (reserveEth, reserveDai) : (reserveDai, reserveEth);
    (reserveA, reserveB) = tokenA == token0 ? (reserve0, reserve1) : (reserve1, reserve0);
} // returns (reserveDai, reserveEth);

// performs chained getAmountOut calculations on any number of pairs
function getAmountsOut(address factory, uint amountIn, address[] memory path) internal view returns (uint[] memory amounts) {
    // path = [@eth, @dai]
    require(path.length >= 2, 'UniswapV2Library: INVALID_PATH');
    amounts = new uint[](path.length);
    // amounts[0] = 100 eth
    amounts[0] = amountIn;
    // i == 0
    for (uint i; i < path.length - 1; i++) {
        // (1,000,000 dai, 1000 eth) = getReserves(factory, @eth, @dai)
        (uint reserveIn, uint reserveOut) = getReserves(factory, path[i], path[i + 1]);
        /*
        // given an input amount of an asset and pair reserves, returns the maximum output amount of the other asset
        function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) internal pure returns (uint amountOut) {
            // amountIn = 100 eth
            // reserveIn = 1,000,000 dai
            // reserveOut = 1000 eth

            // 100 > 0 T
            require(amountIn > 0, 'UniswapV2Library: INSUFFICIENT_INPUT_AMOUNT');
            // 1,000,000 > 0 T
            require(reserveIn > 0 && reserveOut > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
            uint amountInWithFee = amountIn.mul(997); // 100 * 997 => amountInWithFee=997,00
            uint numerator = amountInWithFee.mul(reserveOut); // 997,00 * 1,000 => numerator=997,00,000
            uint denominator = reserveIn.mul(1000).add(amountInWithFee); // (1,000,000 * 1,000) + 997,00 => denominator=1,000,099,700
            amountOut = numerator / denominator; // 997,00,000/1,000,099,700 => amountOut=0.0996900609009282 == 9,939,099.071822539292832504 * 1e18
        }
        */
        // 9,939,099.071822539292832504 * 1e18
        amounts[i + 1] = getAmountOut(amounts[i], reserveIn, reserveOut);
    }
}

function swapExactTokensForTokens(
    uint amountIn,
    uint amountOutMin,
    address[] calldata path, // [@eth, @dai]
    address to,
    uint deadline
) external virtual override ensure(deadline) returns (uint[] memory amounts) {
    // amounts[0] = 100 eth, amounts[1] = 9,939,099.071822539292832504
    amounts = UniswapV2Library.getAmountsOut(factory, amountIn, path);
    require(amounts[amounts.length - 1] >= amountOutMin, 'UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT');
    /*
    function safeTransferFrom(
        address token,
        address from,
        address to,
        uint256 value
    ) internal {}
    */
    TransferHelper.safeTransferFrom(
        // @eth, @sender   , @eth/@dai pair                                     , 100 eth
        path[0], msg.sender, UniswapV2Library.pairFor(factory, path[0], path[1]), amounts[0]
    );
    // swapping after sending eth to the @eth/@dai pair
    _swap(amounts, path, to);
}
```

### clarification

**what the contract do?:** the contract swap all input for max output e.g: input => 1000DAI, output => max wETH.

**how it works?:** the function call the `UniswapV2Library.getAmoutsOut(factory, amountIn, path);`
which return array of element named `amounts` first element of the array `amonts[0]` contain the amount of tokens that went in *amountIn*, the last element of the array `amounts[length - 1]` contain the amount of the token that came out in the last swap. if the swap contain multiple swap the array will contain the intermediary swap aswell.

`require(amounts[amounts.length - 1] >= amountOutMin, 'UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT');`, this check that the amount came out is grated or equal to the min amount that the user want *amountOutMin*.

`TransferHelper.safeTransferFrom( path[0], msg.sender, UniswapV2Library.pairFor(factory, path[0], path[1]), amounts[0]);`, the input token is trasfared over to the `pair` contract, the input token will be stored in the `path[0]` and the `pair` contract is computed by taking `path[0]` & `path[1]`, the way it compute the `pair` contract `address` is by using *create2*, and the amount it sent is stored in `amount[0]`. after direct sending token to `pair` contract it `swap` token by calling the internal function `_swap(smounts, path, to)`.

**internal Function `_swap`:**

```javascript
// v2-core contract function: @eth/@dai pair
// this low-level function should be called from a contract which performs important safety checks
function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external lock {
    // amount0Out = 9,939,099.071822539292832504
    // amount1Out = 0 
    // to = @reciver
    // data = nothing
    require(amount0Out > 0 || amount1Out > 0, 'UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT');
    (uint112 _reserve0, uint112 _reserve1,) = getReserves(); // gas savings
    require(amount0Out < _reserve0 && amount1Out < _reserve1, 'UniswapV2: INSUFFICIENT_LIQUIDITY');

    uint balance0;
    uint balance1;
    { // scope for _token{0,1}, avoids stack too deep errors
    address _token0 = token0; // dai
    address _token1 = token1; // eth
    require(to != _token0 && to != _token1, 'UniswapV2: INVALID_TO');
    //                  _safeTransfer(@dai   , @reciver, 9,939,099.071822539292832504)
    if (amount0Out > 0) _safeTransfer(_token0, to, amount0Out); // optimistically transfer tokens
    if (amount1Out > 0) _safeTransfer(_token1, to, amount1Out); // optimistically transfer tokens
    if (data.length > 0) IUniswapV2Callee(to).uniswapV2Call(msg.sender, amount0Out, amount1Out, data);

    balance0 = IERC20(_token0).balanceOf(address(this)); // balance of dai in the @eth/@dai pair
    balance1 = IERC20(_token1).balanceOf(address(this)); // balance of eth in the @eth/@dai pair
    }
    // the remeaning dai balance after transfer the aount to reciver
    uint amount0In = balance0 > _reserve0 - amount0Out ? balance0 - (_reserve0 - amount0Out) : 0;
    // the remeaning eth balance after transfer the aount to reciver
    uint amount1In = balance1 > _reserve1 - amount1Out ? balance1 - (_reserve1 - amount1Out) : 0;
    require(amount0In > 0 || amount1In > 0, 'UniswapV2: INSUFFICIENT_INPUT_AMOUNT');
    { // scope for reserve{0,1}Adjusted, avoids stack too deep errors
    uint balance0Adjusted = balance0.mul(1000).sub(amount0In.mul(3));
    uint balance1Adjusted = balance1.mul(1000).sub(amount1In.mul(3));
    // checking that the lequidity is correct
    require(balance0Adjusted.mul(balance1Adjusted) >= uint(_reserve0).mul(_reserve1).mul(1000**2), 'UniswapV2: K');
    }

    // updating the @eth/@dai pair
    _update(balance0, balance1, _reserve0, _reserve1);
    emit Swap(msg.sender, amount0In, amount1In, amount0Out, amount1Out, to);
}
// requires the initial amount to have already been sent to the first pair
function _swap(
    uint[] memory amounts, // array of amounts where [0] is the amountIn and [n-1] is amountOut every thing between is amount of the inner swaps happens if exists.
    address[] memory path, // array contain the addresses of the tokens of the swaps.
    address _to // the reciver of the amountOut
    ) internal virtual {
    // looping through the tokens and perform swaps for each pair.
    for (uint i; i < path.length - 1; i++) {
        // for the e.g of @eth/@dai this will contain
        // path = [@eth, @dai]
        // amounts[0] = 100 eth, amounts[1] = 9,939,099.071822539292832504
        // (@eth, @dai)
        (address input, address output) = (path[i], path[i + 1]);
        // sortTokens(input, output) returns (@token0, @token1) which is token0 < token1  => (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        // (@dai)
        (address token0,) = UniswapV2Library.sortTokens(input, output);  
        // 9,939,099.071822539292832504
        uint amountOut = amounts[i + 1];
        // (9,939,099.071822539292832504, 0)
        (uint amount0Out, uint amount1Out) = input == token0 ? (uint(0), amountOut) : (amountOut, uint(0));
        // to == reciver
        address to = i < path.length - 2 ? UniswapV2Library.pairFor(factory, output, path[i + 2]) : _to;
        // @eth/@dai.swap(9,939,099.071822539292832504, 0, @reciver, nothing)
        IUniswapV2Pair(UniswapV2Library.pairFor(factory, input, output)).swap(
            amount0Out, amount1Out, to, new bytes(0)
        );
    }
}
```

the `_mint` function take 3 parameters: `uint[] memory amounts`, `address[] memory path`, `address _to`.

let's understand each one of them:

1. `amounts`: array of amounts that conain all the input intermidiary and outputs amount that came from the intir swap.
2. `path`: the addresses of the tokens to swap, path will determin which pair contract will call.
3. `address _to:` this is the address of the reciver of the final output token.

inside the `for loop` it gets the address of the `pair` contract and call the function `swap`.

### Function Add Liq

```javascript
// given some amount of an asset and pair reserves, returns an equivalent amount of the other asset
function quote(uint amountA, uint reserveA, uint reserveB) internal pure returns (uint amountB) {
    require(amountA > 0, 'UniswapV2Library: INSUFFICIENT_AMOUNT');
    require(reserveA > 0 && reserveB > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
    // dy = dx * y0/x0 => given new x token how much y token should equal.
    amountB = amountA.mul(reserveB) / reserveA;
}

// create pair function from V2-core contract UniswapV2Factory.sol
// called once by the factory at time of deployment
function initialize(address _token0, address _token1) external {
    require(msg.sender == factory, 'UniswapV2: FORBIDDEN'); // sufficient check
    token0 = _token0;
    token1 = _token1;
}

// what this function dose is it create a pairV2 contract that manage and swap tokens adding and removing liquidity.
function createPair(address tokenA, address tokenB) external returns (address pair) {
    require(tokenA != tokenB, 'UniswapV2: IDENTICAL_ADDRESSES');
    // @tokenA & @tokenB are 160bit which can converted to adress and vice verca 
    // this sort the tokens in assendant order where token with small address placed first.
    (address token0, address token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
    require(token0 != address(0), 'UniswapV2: ZERO_ADDRESS');
    require(getPair[token0][token1] == address(0), 'UniswapV2: PAIR_EXISTS'); // single check is sufficient
    // creationCode = runtime code(code that executed when tx is sent) + constructor args.
    bytes memory bytecode = type(UniswapV2Pair).creationCode; // Memory byte array that contains the creation bytecode of the contract.
    bytes32 salt = keccak256(abi.encodePacked(token0, token1));
    assembly {
        // this use create2; to calculate the pair contract @ before it's deployed.
        pair := create2(0, add(bytecode, 32), mload(bytecode), salt)
    }
    IUniswapV2Pair(pair).initialize(token0, token1);
    getPair[token0][token1] = pair;
    getPair[token1][token0] = pair; // populate mapping in the reverse direction
    allPairs.push(pair);
    emit PairCreated(token0, token1, pair, allPairs.length);
}

// adding liquidity from V2-periphery contract UniswapV2Router02.sol
function _addLiquidity(
    address tokenA,
    address tokenB,
    uint amountADesired,
    uint amountBDesired,
    uint amountAMin,
    uint amountBMin
) internal virtual returns (uint amountA, uint amountB) {
    // create the pair if it doesn't exist yet
    if (IUniswapV2Factory(factory).getPair(tokenA, tokenB) == address(0)) {
        IUniswapV2Factory(factory).createPair(tokenA, tokenB);
    }
    (uint reserveA, uint reserveB) = UniswapV2Library.getReserves(factory, tokenA, tokenB);
    if (reserveA == 0 && reserveB == 0) {
        (amountA, amountB) = (amountADesired, amountBDesired);
    } else {
        uint amountBOptimal = UniswapV2Library.quote(amountADesired, reserveA, reserveB);
        if (amountBOptimal <= amountBDesired) {
            require(amountBOptimal >= amountBMin, 'UniswapV2Router: INSUFFICIENT_B_AMOUNT');
            (amountA, amountB) = (amountADesired, amountBOptimal);
        } else {
            uint amountAOptimal = UniswapV2Library.quote(amountBDesired, reserveB, reserveA);
            assert(amountAOptimal <= amountADesired);
            require(amountAOptimal >= amountAMin, 'UniswapV2Router: INSUFFICIENT_A_AMOUNT');
            (amountA, amountB) = (amountAOptimal, amountBDesired);
        }
    }
}

// this function handle ERC20 & ERC20 pair.
function addLiquidity(
    address tokenA, // tokens the user gonna add.
    address tokenB, // tokens the user gonna add.
    uint amountADesired, // the amount of token the user gonna add.
    uint amountBDesired, // the amount of token the user gonna add.
    uint amountAMin, // the min amount that should be diposited.
    uint amountBMin, // the min amount that should be diposited.
    address to, // the pool shairs @
    uint deadline
) external virtual override ensure(deadline) returns (uint amountA, uint amountB, uint liquidity) {
    (amountA, amountB) = _addLiquidity(tokenA, tokenB, amountADesired, amountBDesired,amountAMin, amountBMin);
    address pair = UniswapV2Library.pairFor(factory, tokenA, tokenB);
    TransferHelper.safeTransferFrom(tokenA, msg.sender, pair, amountA);
    TransferHelper.safeTransferFrom(tokenB, msg.sender, pair, amountB);
    liquidity = IUniswapV2Pair(pair).mint(to);
}

// the only diff from the addLiq function is that it convert eth to weth.
function addLiquidityETH(
    address token,
    uint amountTokenDesired,
    uint amountTokenMin,
    uint amountETHMin,
    address to,
    uint deadline
) external virtual override payable ensure(deadline) returns (uint amountToken, uint amountETH, uint liquidity) {
    (amountToken, amountETH) = _addLiquidity(
        token,
        WETH,
        amountTokenDesired,
        msg.value,
        amountTokenMin,
        amountETHMin
    );
    address pair = UniswapV2Library.pairFor(factory, token, WETH);
    TransferHelper.safeTransferFrom(token, msg.sender, pair, amountToken);
    IWETH(WETH).deposit{value: amountETH}();
    assert(IWETH(WETH).transfer(pair, amountETH));
    liquidity = IUniswapV2Pair(pair).mint(to);
    // refund dust eth, if any
    if (msg.value > amountETH) TransferHelper.safeTransferETH(msg.sender, msg.value - amountETH);
}

// this low-level function should be called from a contract which performs important safety checks
function mint(address to) external lock returns (uint liquidity) {
    (uint112 _reserve0, uint112 _reserve1,) = getReserves(); // gas savings
    uint balance0 = IERC20(token0).balanceOf(address(this));
    uint balance1 = IERC20(token1).balanceOf(address(this));
    uint amount0 = balance0.sub(_reserve0);
    uint amount1 = balance1.sub(_reserve1);

    // check the white paper for the how to calculate minFee MATH.
    bool feeOn = _mintFee(_reserve0, _reserve1);
    uint _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply canupdate in _mintFee
    if (_totalSupply == 0) {
        //pool value function f(x,y) = sqrt(xy).
        liquidity = Math.sqrt(amount0.mul(amount1)).sub(MINIMUM_LIQUIDITY);
        // protect against "vault inflation attack" @> neet tosearch about.
        _mint(address(0), MINIMUM_LIQUIDITY); // permanently lock the first MINIMUM_LIQUIDITY tokens
    } else {
        liquidity = Math.min(amount0.mul(_totalSupply) / _reserve0, amount1.mul(_totalSupply) /_reserve1);
    }
    require(liquidity > 0, 'UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED');
    _mint(to, liquidity);

    _update(balance0, balance1, _reserve0, _reserve1);
    if (feeOn) kLast = uint(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
    emit Mint(msg.sender, amount0, amount1);
}
```

## Function Remove Liq

```javascript
function _burn(address from, uint value) internal {
     balanceOf[from] = balanceOf[from].sub(value);
     totalSupply = totalSupply.sub(value);
     emit Transfer(from, address(0), value);
 }
// this low-level function should be called from a contract which performs important safety checks
 function burn(address to) external lock returns (uint amount0, uint amount1) {
     (uint112 _reserve0, uint112 _reserve1,) = getReserves(); // gas savings
     address _token0 = token0;                                // gas savings
     address _token1 = token1;                                // gas savings
     uint balance0 = IERC20(_token0).balanceOf(address(this));
     uint balance1 = IERC20(_token1).balanceOf(address(this));
     uint liquidity = balanceOf[address(this)];

     bool feeOn = _mintFee(_reserve0, _reserve1);
     uint _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
     amount0 = liquidity.mul(balance0) / _totalSupply; // using balances ensures pro-rata distribution
     amount1 = liquidity.mul(balance1) / _totalSupply; // using balances ensures pro-rata distribution
     require(amount0 > 0 && amount1 > 0, 'UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED');
     _burn(address(this), liquidity);
     _safeTransfer(_token0, to, amount0);
     _safeTransfer(_token1, to, amount1);
     balance0 = IERC20(_token0).balanceOf(address(this));
     balance1 = IERC20(_token1).balanceOf(address(this));

     _update(balance0, balance1, _reserve0, _reserve1);
     if (feeOn) kLast = uint(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
     emit Burn(msg.sender, amount0, amount1, to);
 }
// remving the Liq
 function removeLiquidity(
        address tokenA, // token @ for wETH for e.g
        address tokenB, // token @ for DAI for e.g
        uint liquidity, // the liquidity
        uint amountAMin, // min amount A
        uint amountBMin, // min amount B
        address to, // @ of the reciver
        uint deadline
    ) public virtual override ensure(deadline) returns (uint amountA, uint amountB) {
        // selcting the pair for the token A/B
        address pair = UniswapV2Library.pairFor(factory, tokenA, tokenB);
        IUniswapV2Pair(pair).transferFrom(msg.sender, pair, liquidity); // send liquidity to pair
        // burn the amount that given from the reciver
        (uint amount0, uint amount1) = IUniswapV2Pair(pair).burn(to);
        // sorting token asc order
        (address token0,) = UniswapV2Library.sortTokens(tokenA, tokenB);
        // sorting the amounts based on the token order
        (amountA, amountB) = tokenA == token0 ? (amount0, amount1) : (amount1, amount0);
        require(amountA >= amountAMin, 'UniswapV2Router: INSUFFICIENT_A_AMOUNT');
        require(amountB >= amountBMin, 'UniswapV2Router: INSUFFICIENT_B_AMOUNT');
    }
```
