// SPDX-License-Identifier: MIT
pragma solidity >=0.6.0;

interface AggregatorV3Interface {

  function decimals() external view returns (uint8);
  function description() external view returns (string memory);
  function version() external view returns (uint256);

  // getRoundData and latestRoundData should both raise "No data present"
  // if they do not have data to report, instead of returning unset values
  // which could be misinterpreted as actual reported values.
  function getRoundData(uint80 _roundId)
    external
    view
    returns (
      uint80 roundId,
      int256 answer,
      uint256 startedAt,
      uint256 updatedAt,
      uint80 answeredInRound
    );
  function latestRoundData()
    external
    view
    returns (
      uint80 roundId,
      int256 answer,
      uint256 startedAt,
      uint256 updatedAt,
      uint80 answeredInRound
    );

}
pragma solidity >=0.5.0;

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}
pragma solidity >=0.5.0;





library UniswapV2Library {
    using SafeMath for uint;

    // returns sorted token addresses, used to handle return values from pairs sorted in this order
    function sortTokens(address tokenA, address tokenB) internal pure returns (address token0, address token1) {
        require(tokenA != tokenB, 'UniswapV2Library: IDENTICAL_ADDRESSES');
        (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        require(token0 != address(0), 'UniswapV2Library: ZERO_ADDRESS');
    }

    // calculates the CREATE2 address for a pair without making any external calls
    function pairFor(address factory, address tokenA, address tokenB) internal pure returns (address pair) {
        (address token0, address token1) = sortTokens(tokenA, tokenB);
        pair = address(uint(keccak256(abi.encodePacked(
                hex'ff',
                factory,
                keccak256(abi.encodePacked(token0, token1)),
//                hex'3f88503e8580ab941773b59034fb4b2a63e86dbc031b3633a925533ad3ed2b93' // honeyswap deploy init code hash
                hex'96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f' // original init code hash
            ))));
    }

    // fetches and sorts the reserves for a pair
    function getReserves(address factory, address tokenA, address tokenB) internal view returns (uint reserveA, uint reserveB) {
        (address token0,) = sortTokens(tokenA, tokenB);
        (uint reserve0, uint reserve1,) = IUniswapV2Pair(pairFor(factory, tokenA, tokenB)).getReserves();
        (reserveA, reserveB) = tokenA == token0 ? (reserve0, reserve1) : (reserve1, reserve0);
    }

    // given some amount of an asset and pair reserves, returns an equivalent amount of the other asset
    function quote(uint amountA, uint reserveA, uint reserveB) internal pure returns (uint amountB) {
        require(amountA > 0, 'UniswapV2Library: INSUFFICIENT_AMOUNT');
        require(reserveA > 0 && reserveB > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
        amountB = amountA.mul(reserveB) / reserveA;
    }

    // given an input amount of an asset and pair reserves, returns the maximum output amount of the other asset
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) internal pure returns (uint amountOut) {
        require(amountIn > 0, 'UniswapV2Library: INSUFFICIENT_INPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
        uint amountInWithFee = amountIn.mul(997);
        uint numerator = amountInWithFee.mul(reserveOut);
        uint denominator = reserveIn.mul(1000).add(amountInWithFee);
        amountOut = numerator / denominator;
    }

    // given an output amount of an asset and pair reserves, returns a required input amount of the other asset
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) internal pure returns (uint amountIn) {
        require(amountOut > 0, 'UniswapV2Library: INSUFFICIENT_OUTPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
        uint numerator = reserveIn.mul(amountOut).mul(1000);
        uint denominator = reserveOut.sub(amountOut).mul(997);
        amountIn = (numerator / denominator).add(1);
    }

    // performs chained getAmountOut calculations on any number of pairs
    function getAmountsOut(address factory, uint amountIn, address[] memory path) internal view returns (uint[] memory amounts) {
        require(path.length >= 2, 'UniswapV2Library: INVALID_PATH');
        amounts = new uint[](path.length);
        amounts[0] = amountIn;
        for (uint i; i < path.length - 1; i++) {
            (uint reserveIn, uint reserveOut) = getReserves(factory, path[i], path[i + 1]);
            amounts[i + 1] = getAmountOut(amounts[i], reserveIn, reserveOut);
        }
    }

    // performs chained getAmountIn calculations on any number of pairs
    function getAmountsIn(address factory, uint amountOut, address[] memory path) internal view returns (uint[] memory amounts) {
        require(path.length >= 2, 'UniswapV2Library: INVALID_PATH');
        amounts = new uint[](path.length);
        amounts[amounts.length - 1] = amountOut;
        for (uint i = path.length - 1; i > 0; i--) {
            (uint reserveIn, uint reserveOut) = getReserves(factory, path[i - 1], path[i]);
            amounts[i - 1] = getAmountIn(amounts[i], reserveIn, reserveOut);
        }
    }
}
pragma solidity ^0.7.0;

interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}



abstract contract LiquidityInfo {
    using SafeMath for uint256;

    address internal factory;
    IFactory internal Factory;

    constructor() {
        factory = 0xA818b4F111Ccac7AA31D0BCc0806d64F2E0737D7;
        Factory = IFactory(factory);
    }

    function pairInfo(address tokenA, address tokenB) public view returns (uint reserveA, uint reserveB) {
       (address token0,) = UniswapV2Library.sortTokens(tokenA, tokenB);
       IUniswapV2Pair pair = IUniswapV2Pair(Factory.getPair(tokenA, tokenB));
       (uint reserve0, uint reserve1,) = pair.getReserves();
       (reserveA, reserveB) = tokenA == token0 ? (reserve0, reserve1) : (reserve1, reserve0);
     }
        // performs chained getAmountIn calculations on any number of pairs
    function amountInForExactOut(uint amountOut, address[] memory path) internal view returns (uint) {
        require(path.length >= 2, 'UniswapV2Library: INVALID_PATH');
        uint[] memory amounts;
        amounts = new uint[](path.length);
        amounts[amounts.length - 1] = amountOut;
        for (uint i = path.length - 1; i > 0; i--) {
            (uint reserveIn, uint reserveOut) = pairInfo(path[i - 1], path[i]);
            amounts[i - 1] = UniswapV2Library.getAmountIn(amounts[i], reserveIn, reserveOut);
        }
        return amounts[0];
    }

}
interface IFactory {
  function getPair(address tokenA, address tokenB) external view returns (address pair);
}












abstract contract LivePrice {

    mapping(address => AggregatorV3Interface) internal priceFeed;

    /**
     * Network: xDai MainNet
     */

    /**
     * Returns the latest price
     */
    function getLatestPrice(address token) internal view returns (int) {
        (
            ,
            int price,
            ,
            uint timeStamp,

        ) = priceFeed[token].latestRoundData();
        // If the round is not complete yet, timestamp is 0
        require(timeStamp > 0, "Round not complete");
        return price;
    }

    function addPriceFeed(address token, address aggregator) internal {
      priceFeed[token] = AggregatorV3Interface(aggregator);
    }
}

interface IERC20EXT is IERC20 {
    function decimals() external view returns (uint8);
}

 contract PaymentSystem is Ownable, LiquidityInfo, LivePrice {
  using SafeMath for uint256;

  mapping(address => IERC20EXT) internal token;

  address[] public merchant;
  mapping(address => address) public tokenToReceive;
  UniswapV2RouterInterface SwapRouter;
  uint256 oracleDecimals;
  mapping(address => mapping(address => address[])) swapPath;

  constructor() {
    SwapRouter = UniswapV2RouterInterface(0x1C232F01118CB8B424793ae03F870aa7D0ac7f77);
    address xDai = 0xe91D153E0b41518A2Ce8Dd3D7944Fa863463a97d;
    address ETH = 0x6A023CCd1ff6F2045C3309768eAd9E68F978f6e1;
    address BTC = 0x8e5bBbb09Ed1ebdE8674Cda39A0c169401db4252;
    address USDC = 0xDDAfbb505ad214D7b80b1f830fcCc89B60fb7A83;
    addPaymentToken(xDai, 0x678df3415fc31947dA4324eC63212874be5a82f8); // xDai
    addPaymentToken(ETH, 0xa767f745331D267c7751297D982b050c93985627); // Ether
    addPaymentToken(BTC, 0x6C1d7e76EF7304a40e8456ce883BC56d3dEA3F7d); // Bitcoin
    addPaymentToken(USDC, 0x26C31ac71010aF62E6B486D1132E266D6298857D); // USD Coin
    oracleDecimals = 10**8;
    swapPath[xDai][BTC] = [xDai, ETH, BTC];
    swapPath[ETH][USDC] = [ETH, xDai, USDC];
    swapPath[BTC][xDai] = [BTC, ETH, xDai];
    swapPath[BTC][USDC] = [BTC, ETH, xDai, USDC];
    swapPath[USDC][ETH] = [USDC, xDai, ETH];
    swapPath[USDC][BTC] = [USDC, xDai, ETH, BTC];
  }

  function pay(address _merchant, uint256 _amountRequested, address _userPaymentToken, uint256 _slippage, bool _safeSwap) public {
    (bool _isMerchant,) = isMerchant(_merchant);
    require(_isMerchant, "[Unknown merchant address]");
    require(isPaymentToken(_userPaymentToken), "[Token not supported]");
    require(0 <= _slippage && _slippage <= 100, "[Slippage value out of range]");
    if(_userPaymentToken == tokenToReceive[_merchant]){
      require(token[_userPaymentToken].allowance(msg.sender, address(this)) >= _amountRequested, "[Insufficient allowance for user payment token]");
      require(token[_userPaymentToken].transferFrom(msg.sender, _merchant, _amountRequested), "[Value not received from customer]");
    }
    else {
      (uint256 amountToMerchant, uint256 amountToRefund) = swapExactOut(_userPaymentToken, tokenToReceive[_merchant], _amountRequested, _slippage, 0, _safeSwap);
      if(tokenToReceive[_merchant] == SwapRouter.WETH()){
        (bool sent,) = _merchant.call{value: amountToMerchant}(""); // Send xDai to merchant
        require(sent, "[Failed to send xDai]");
      }
      else {
          token[tokenToReceive[_merchant]].transferFrom(address(this), _merchant, amountToMerchant); // Send tokens to merchant
      }
      token[_userPaymentToken].transferFrom(address(this), msg.sender, amountToRefund); // Refund unused tokens to caller
    }
  }

  function payXDAI(address _merchant, uint256 _amountRequested, uint256 _slippage, bool _safeSwap) public payable {
    (bool _isMerchant,) = isMerchant(_merchant);
    require(_isMerchant, "[Unknown merchant address]");
    require(msg.value > 0, "[No value sent]");
    if(SwapRouter.WETH() == tokenToReceive[_merchant]){
      require(msg.value == _amountRequested, "[Amount sent not matching amount requested]");
      (bool sent,) = _merchant.call{value: _amountRequested}("");
      require(sent, "[Failed to send xDai]");
    }
    else {
      (uint256 amountToMerchant, uint256 amountToRefund) = swapExactOut(SwapRouter.WETH(), tokenToReceive[_merchant], _amountRequested, _slippage, msg.value, _safeSwap);
      token[tokenToReceive[_merchant]].transferFrom(address(this), _merchant, amountToMerchant); // Send tokens to merchant
      (bool sent,) = msg.sender.call{value: amountToRefund}(""); // Refund leftover tokens to customer
      require(sent, "[Failed to refund xDai]");
    }
  }

    function addMerchant(address _paymentAddress, address _paymentToken)
  public
  onlyOwner
  {
    (bool _isMerchant,) = isMerchant(_paymentAddress);
    require(!_isMerchant, "[Merchant already exists]");
    require(isPaymentToken(_paymentToken), "[Token not supported]");
    merchant.push(_paymentAddress);
    tokenToReceive[_paymentAddress] = _paymentToken;
  }

  function removeMerchant(address _merchant) public onlyOwner {
      (bool _isMerchant, uint256 s) = isMerchant(_merchant);
      if(_isMerchant){
          merchant[s] = merchant[merchant.length - 1];
          merchant.pop();
      }
  }

  function addPaymentToken(address _token, address _chainlinkPriceFeed)
  public
  onlyOwner
  {
    require(!isPaymentToken(_token), "[Token already accepted]");
    token[_token] = IERC20EXT(_token);
    addPriceFeed(_token, _chainlinkPriceFeed);
  }

  function changePaymentTokenFor(address _merchant, address _newPaymentToken) public onlyOwner {
    (bool _isMerchant,) = isMerchant(_merchant);
    require(_isMerchant, "[Address is not a registered merchant]");
    require(isPaymentToken(_newPaymentToken), "[Token not supported]");
    tokenToReceive[_merchant] = _newPaymentToken;
  }

  function setSwapPath(address _tokenIn, address _tokenOut, address[] memory path) public onlyOwner {
      require(path.length >= 2, "[Invalid path length]");
      require(path[0] == _tokenIn && path[path.length.sub(1)] == _tokenOut, "[Invalid input/output for given path]");
      swapPath[_tokenIn][_tokenOut] = path;
  }

  function isPaymentToken(address _token)
      public
      view
      returns(bool)
  {
    if (_token == address(token[_token])) return (true);
    return (false);
  }

  function isMerchant(address _merchant) internal view returns(bool, uint256)
      {
          for (uint256 s = 0; s < merchant.length; s += 1){
              if (_merchant == merchant[s]) return (true, s);
          }
          return (false, 0);
      }



  function swapExactOut(address _fromToken, address _toToken, uint256 _amountOut, uint256 _slippage, uint256 _msgValue, bool _safeSwap)
  internal
  returns(uint256, uint256)
  {
    address[] memory path;
    if(swapPath[_fromToken][_toToken].length > 2) {
        path = swapPath[_fromToken][_toToken];
    }
    else {
        path = new address[](2);
        path[0] = _fromToken;
        path[1] = _toToken;
    }

    uint[] memory amounts;

    uint256 amountInMax = calculateMaxIn(_amountOut, path, _slippage); // Decentralized exchange value call
    if(_safeSwap) require(checkPriceRange(_fromToken, _toToken, amountInForExactOut(_amountOut, path), _amountOut), "[Transaction rejected due to price fluctuations]"); // Check if it matches with live prices from oracle

    if(_fromToken == SwapRouter.WETH()){
      require(_msgValue >= amountInMax, "[Amount sent less than amount requested]");
      amounts = SwapRouter.swapETHForExactTokens{value: _msgValue}(_amountOut, path, address(this), block.timestamp.add(30));
      return(amounts[amounts.length - 1], _msgValue.sub(amounts[0]));
    }
    else if(_toToken == SwapRouter.WETH()){
      require(token[_fromToken].allowance(msg.sender, address(this)) >= amountInMax, "[Insufficient allowance for user payment token]");
      require(token[_fromToken].transferFrom(msg.sender, address(this), amountInMax), "[Value not received from customer]");
      require(token[_fromToken].approve(address(SwapRouter), amountInMax), "[Approve failed]");
      amounts = SwapRouter.swapTokensForExactETH(_amountOut, amountInMax, path, address(this), block.timestamp.add(30));
      return(amounts[amounts.length - 1], amountInMax.sub(amounts[0]));
    }
    else {
      require(token[_fromToken].allowance(msg.sender, address(this)) >= amountInMax, "[Insufficient allowance for user payment token]");
      require(token[_fromToken].transferFrom(msg.sender, address(this), amountInMax), "[Value not received from customer]");
      require(token[_fromToken].approve(address(SwapRouter), amountInMax), "[Approve failed]");
      amounts = SwapRouter.swapTokensForExactTokens(_amountOut, amountInMax, path, address(this), block.timestamp.add(30));
      return(amounts[amounts.length - 1], amountInMax.sub(amounts[0]));
    }


  }

  function calculateMaxIn(uint256 _amountOut, address[] memory _path, uint256 _slippage)
  public
  view
  returns (uint256)
  {
    uint256 amountIn = amountInForExactOut(_amountOut, _path);
    amountIn = amountIn.add(amountIn.div(100).mul(_slippage)); // Implement user requested slippage
    return amountIn;
  }

  function checkPriceRange(address _fromToken, address _toToken, uint256 _amountIn, uint256 _amountOut) public view returns(bool check) {
    uint256 fromPriceOracle = uint(getLatestPrice(_fromToken));
    uint256 toPriceOracle = uint(getLatestPrice(_toToken));
    uint8 decimalsIn = token[_fromToken].decimals();
    uint8 decimalsOut = token[_toToken].decimals();
    uint256 valueIn;
    uint256 valueOut;
    if(decimalsIn != decimalsOut){
        if(decimalsIn > decimalsOut){
            valueIn = _amountIn.mul(fromPriceOracle).div(oracleDecimals);
            valueOut = _amountOut.mul(toPriceOracle).mul(10**(decimalsIn - decimalsOut)).div(oracleDecimals);
        }
        else {
            valueIn = _amountIn.mul(fromPriceOracle).mul(10**(decimalsOut - decimalsIn)).div(oracleDecimals);
            valueOut = _amountOut.mul(toPriceOracle).div(oracleDecimals);
        }
    }
    else {
        valueIn = _amountIn.mul(fromPriceOracle).div(oracleDecimals);
        valueOut = _amountOut.mul(toPriceOracle).div(oracleDecimals);
    }

    if(valueIn > valueOut) {
      uint256 difference = valueIn.sub(valueOut);
      if(valueIn.div(20) < difference) check = false; // If more than 5% difference
      else check = true;
    }
    else check = true;
  }

  receive() external payable {}

}
interface UniswapV2RouterInterface {
function swapTokensForExactTokens(
  uint amountOut,
  uint amountInMax,
  address[] calldata path,
  address to,
  uint deadline
) external returns (uint[] memory amounts);
function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
  external
  returns (uint[] memory amounts);
  function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
  external
  payable
  returns (uint[] memory amounts);
  function WETH() external pure returns (address);
}
