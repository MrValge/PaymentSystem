// SPDX-License-Identifier: MIT

pragma solidity ^0.7.0;

import "IERC20.sol";
import "Ownable.sol";
import "SafeMath.sol";
import "UniswapLiquidityInterface.sol";
import "LivePrice.sol";

 contract PaymentSystem is Ownable, LiquidityInfo, LivePrice {
  using SafeMath for uint256;

  mapping(address => IERC20) internal token;

  address[] public merchant;
  mapping(address => address) public tokenToReceive;
  UniswapV2RouterInterface SwapRouter;

  constructor() {
    SwapRouter = UniswapV2RouterInterface(0x1C232F01118CB8B424793ae03F870aa7D0ac7f77);

    addPaymentToken(0xe91D153E0b41518A2Ce8Dd3D7944Fa863463a97d, 0x678df3415fc31947dA4324eC63212874be5a82f8); // xDai
    addPaymentToken(0x6A023CCd1ff6F2045C3309768eAd9E68F978f6e1, 0xa767f745331D267c7751297D982b050c93985627); // Ether
    addPaymentToken(0x8e5bBbb09Ed1ebdE8674Cda39A0c169401db4252, 0x6C1d7e76EF7304a40e8456ce883BC56d3dEA3F7d); // Bitcoin
    addPaymentToken(0xDDAfbb505ad214D7b80b1f830fcCc89B60fb7A83, 0x26C31ac71010aF62E6B486D1132E266D6298857D); // USD Coin
  }

  function addPaymentToken(address _token, address _chainlinkPriceFeed)
  public
  onlyOwner
  {
    require(!isPaymentToken(_token), "[Token already accepted]");
    token[_token] = IERC20(_token);
    addPriceFeed(_token, _chainlinkPriceFeed);
  }

  function isPaymentToken(address _token)
      public
      view
      returns(bool)
  {
    if (_token == address(token[_token])) return (true);
    return (false);
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

  function isMerchant(address _merchant) internal view returns(bool, uint256)
      {
          for (uint256 s = 0; s < merchant.length; s += 1){
              if (_merchant == merchant[s]) return (true, s);
          }
          return (false, 0);
      }

  function changePaymentTokenFor(address _merchant, address _newPaymentToken) public onlyOwner {
    (bool _isMerchant,) = isMerchant(_merchant);
    require(_isMerchant, "[Address is not a registered merchant]");
    require(isPaymentToken(_newPaymentToken), "[Token not supported]");
    tokenToReceive[_merchant] = _newPaymentToken;
  }

  function pay(address _merchant, uint256 _amountRequested, address _userPaymentToken) public {
    (bool _isMerchant,) = isMerchant(_merchant);
    require(_isMerchant, "[Unknown merchant address]");
    require(isPaymentToken(_userPaymentToken), "[Token not supported]");
    if(_userPaymentToken == tokenToReceive[_merchant]){
      require(token[_userPaymentToken].allowance(msg.sender, address(this)) >= _amountRequested, "[Insufficient allowance for user payment token]");
      require(token[_userPaymentToken].transferFrom(msg.sender, _merchant, _amountRequested), "[Value not received from customer]");
    }
    else {
      (uint256 amountToMerchant, uint256 amountToRefund) = swapExactOut(_userPaymentToken, tokenToReceive[_merchant], _amountRequested, 0);
      if(tokenToReceive[_merchant] == SwapRouter.WETH()){
        (bool sent,) = _merchant.call{value: amountToMerchant}(""); // Send xDai to merchant
        require(sent, "[Failed to send xDai]");
      }
      else require(token[tokenToReceive[_merchant]].transferFrom(address(this), _merchant, amountToMerchant), "[Post swap token transfer error]"); // Send tokens to merchant

      token[_userPaymentToken].transferFrom(address(this), msg.sender, amountToRefund); // Refund unused tokens to caller
    }
  }

  function payXDAI(address _merchant, uint256 _amountRequested) public payable {
    (bool _isMerchant,) = isMerchant(_merchant);
    require(_isMerchant, "[Unknown merchant address]");
    require(msg.value > 0, "[No value sent]");
    if(SwapRouter.WETH() == tokenToReceive[_merchant]){
      require(msg.value == _amountRequested, "[Amount sent not matching amount requested]");
      (bool sent,) = _merchant.call{value: _amountRequested}("");
      require(sent, "[Failed to send xDai]");
    }
    else {
      (uint256 amountToMerchant, uint256 amountToRefund) = swapExactOut(SwapRouter.WETH(), tokenToReceive[_merchant], _amountRequested, msg.value);
      token[tokenToReceive[_merchant]].transferFrom(address(this), _merchant, amountToMerchant); // Send tokens to merchant
      (bool sent,) = msg.sender.call{value: amountToRefund}(""); // Refund leftover tokens to customer
      require(sent, "[Failed to refund xDai]");
    }
  }

  function swapExactOut(address _fromToken, address _toToken, uint256 _amountOut, uint256 _msgValue)
  internal
  returns(uint256, uint256)
  {
    // amountInMax must be retrieved from an oracle of some kind
    address[] memory path = new address[](2);
    path[0] = _fromToken;
    path[1] = _toToken;

    uint[] memory amounts;

    uint256 amountInMax = calculateMaxIn(_fromToken, _toToken, _amountOut); // Decentralized exchange value call
    require(checkPriceRange(_fromToken, _toToken, _amountOut), "[Transaction rejected due to price fluctuations]"); // Check if it matches with live prices from oracle

    if(_fromToken == SwapRouter.WETH()){
      require(_msgValue >= amountInMax, "[Amount sent less than amount requested]");
      amounts = SwapRouter.swapETHForExactTokens{value: _msgValue}(_amountOut, path, address(this), block.timestamp);
      return(amounts[amounts.length - 1], _msgValue.sub(amounts[0]));
    }
    else if(_toToken == SwapRouter.WETH()){
      require(token[_fromToken].allowance(msg.sender, address(this)) >= amountInMax, "[Insufficient allowance for user payment token]");
      require(token[_fromToken].transferFrom(msg.sender, address(this), amountInMax), "[Value not received from customer]");
      require(token[_fromToken].approve(address(SwapRouter), amountInMax), "[Approve failed]");
      amounts = SwapRouter.swapTokensForExactETH(_amountOut, amountInMax, path, address(this), block.timestamp);
      return(amounts[amounts.length - 1], amountInMax.sub(amounts[0]));
    }
    else {
      require(token[_fromToken].allowance(msg.sender, address(this)) >= amountInMax, "[Insufficient allowance for user payment token]");
      require(token[_fromToken].transferFrom(msg.sender, address(this), amountInMax), "[Value not received from customer]");
      require(token[_fromToken].approve(address(SwapRouter), amountInMax), "[Approve failed]");
      amounts = SwapRouter.swapTokensForExactTokens(_amountOut, amountInMax, path, address(this), block.timestamp);
      return(amounts[amounts.length - 1], amountInMax.sub(amounts[0]));
    }


  }

  function calculateMaxIn(address _fromToken, address _toToken, uint256 _amountOut)
  public
  view
  returns (uint256)
  {
    uint256 amountIn = amountInForExactOut(_fromToken, _toToken, _amountOut);
    amountIn = amountIn.add(amountIn.div(100).mul(2)); // +2% margin
    return amountIn;
  }

  function checkPriceRange(address _fromToken, address _toToken, uint256 _amountOut) internal view returns(bool check) {
    uint256 amountIn = amountInForExactOut(_fromToken, _toToken, _amountOut);
    uint256 fromPriceOracle = uint(getLatestPrice(_fromToken));
    uint256 toPriceOracle = uint(getLatestPrice(_toToken));
    uint256 valueIn = amountIn.mul(fromPriceOracle);
    uint256 valueOut = _amountOut.mul(toPriceOracle);
    if(valueIn > valueOut) {
      uint256 difference = valueIn.sub(valueOut);
      if(valueIn.div(100) < difference) check = false; // If more than 1% difference
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
