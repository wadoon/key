// Poblem of BUGGY... contract fixed by adding
// notBy(bid.bidder)
// to makeBid()
// Probably still buggy, see makeBid()

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
* The contract transfers funds or goods directly!
*/

contract OneAuction {

    // Handling mode of the auction
    enum AuctionMode { NeverStarted, Open, Closed }    

    // Handling auction information
    struct AuctionInformation {
        AuctionMode mode;
        address /* payable */ owner;
        uint closingTime;
    }

    // Handling bid information
    struct BidInformation {
        address /* payable */ bidder;
        uint value;
    }


    /*@ invariant
      @   address(this) != auction.owner,
      @   address(this) != bid.bidder;
      @*/
    // I wanted to include bid.bidder != auction.owner, but that is violated by openAuction().
    // Let's see whether that is a problem.
    

    /* Recall:
     * net(addr) := (funds sent from addr to this) - (funds sent from this to addr)
     */
    
    /*@ invariant
      @   bid.value == net(bid.bidder) + net(auction.owner),
      @   (\forall address a;
      @                (a != auction.owner && a != bid.bidder && a != address(this))
      @            ==> net(a) == 0),
      @   net(auction.owner) <= 0,
      @   auction.mode == Open ==> net(auction.owner) == 0,
      @   net(auction.owner) < 0 ==> bid.value == 0;   // not sure this is needed
      @*/
    // State of auction
    AuctionInformation private auction;
    BidInformation private bid;
    
    // Modifier to check mode of auction
    modifier inMode(AuctionMode _auctionMode) {
        require (auction.mode == _auctionMode);
        _;
    }

    modifier by(address _caller) {
        require (msg.sender == _caller);
        _;
    }

    modifier notBy(address _caller) {
        require (msg.sender != _caller);
        _;
    }


    // why not "auction.owner = msg.sender;" instead of passing _owner? 
    constructor (address /* payable */ _owner) 
        public
    {
        auction.mode = AuctionMode.NeverStarted;
        auction.owner = _owner;
    }
    
    function openAuction(uint _closingTime) 
        public
        inMode(AuctionMode.NeverStarted)
        by(auction.owner)
    {
        require (_closingTime > now);

        auction.mode = AuctionMode.Open;
        auction.closingTime = _closingTime;

        bid.value = 0;
        bid.bidder = auction.owner;
    }

    
    /*@ succeeds_only_if
      @   auction.mode == AuctionMode.Open, // inMode(AuctionMode.Open) 
      @   msg.sender != auction.owner,      // notBy(auction.owner)
      @   msg.sender != bid.bidder,         // notBy(bid.bidder)
      @   msg.value > bid.value,
      @   now <= auction.closingTime;
      @ after_success
      @   bid.value > \old(bid.value),
      @   net(bid.bidder) == msg.value,
      @   net(\old(bid.bidder)) == 0;
      @*/
    function makeBid()
        public
        /* payable */
        inMode(AuctionMode.Open) 
        notBy(auction.owner)
        notBy(bid.bidder)
    {
	require (msg.value > bid.value);
        require (now <= auction.closingTime);

	// Transfer the old bid to the old bidder
	uint tmp = bid.value;
	address oldBidder = bid.bidder; 
    // Set the new bid
    uint val = msg.value;
    bid.value = val;
    address sender = msg.sender;
    bid.bidder = sender;
	
	oldBidder.transfer(tmp);
	// Can this be verified, thanks to notBy(bid.bidder)?
	// Probably not. If bid.bidder makes msg.sender calling makeBid().value(1).
	
    }    
    
    /*@ succeeds_only_if
      @   msg.sender == auction.owner || msg.sender == bid.bidder,
      @   now > auction.closingTime;
      @ after_success
      @   net(auction.owner) == -net(bid.bidder);
      @*/
    function closeAuction() 
        public
        inMode(AuctionMode.Open) // reasonable assumtion, but makes locking of funds more likely
    {
        /* require (
            msg.sender == auction.owner || 
            msg.sender == bid.bidder
        );*/
        require (now > auction.closingTime);
        
        auction.mode = AuctionMode.Closed;
        // Transfer the bid to the auction.owner
	uint tmp = bid.value;
        bid.value = 0;	
	auction.owner.transfer(tmp);
    }

}
