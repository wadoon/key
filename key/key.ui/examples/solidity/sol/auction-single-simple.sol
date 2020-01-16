pragma solidity >=0.5.5;

/*
* This class is an example smart contract that is used to conduct auctions.
* It is meant to be an example contract to discuss which properties of
* a smart contract should be verified. It is not necessarily meant to be
* executable.
*
* Participants are stored on the ledger. They can bid for items that are
* being auctioned, and initiate auctions for items they own.
* Any item to be sold or bought within this application has to be recorded in the ledger.
* The contract does not transfer funds or goods directly; rather, it can be seen as
* regulating and recording ownership and payment obligations.
*/

contract OneAuction {
    enum AuctionMode { NeverStarted, Open, Closed }
    // Handling bid information
    struct BidInformation {
        address/* payable */bidder;
        uint value;
    }
    bool public auctionOpen = true;

    uint public currentBid = 0;
    address auctionOwner;
    address currentBidder;
    AuctionMode mode = AuctionMode.Open;
    BidInformation bid;
    
    function closeAuction() public {
        require (msg.sender == auctionOwner);
        require (bid.bidder == currentBidder);
        require (mode == AuctionMode.Open);
        
        uint tmp = currentBid;
        currentBid = 0;
        auctionOwner.transfer(tmp);
    }
    
}
