pragma solidity >=0.5.0 <0.8.0;

import "AggregatorV3Interface.sol";

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
