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

    // Handling mode of the auction
    enum AuctionMode { NeverStarted, Open, Closed }    

    // Handling auction information
    AuctionMode mode;
    address /* payable */ owner;
    uint closingTime;

    // Handling bid information
    address /* payable */ bidder;
    uint value;

    /*@ invariant
      @   address(this) != owner,
      @   address(this) != this.bidder;
      @*/
    // I wanted to include this.bidder != owner, but that is violated by openAuction().
    // Let's see whether that is a problem.

    /* Recall:
     * net(addr) := (funds sent from addr to this) - (funds sent from this to addr)
     */
    
    /*@ invariant
      @   let effective_net(a) be net(a) - withdrawableBalances[a]
      @     in
      @     this.value == effective_net(this.bidder) + effective_net(owner),
      @     (\forall address a;
      @                  (a != owner && a != this.bidder && a != address(this))
      @              ==> effective_net(a) == 0),
      @     effective_net(owner) <= 0,
      @     mode == Open ==> effective_net(owner) == 0,
      @*/

    
    // Withdrawable balances
    mapping (address => uint) withdrawableBalances;


    // Modifier to check mode of auction
    modifier inMode(AuctionMode _auctionMode) {
        require (mode == _auctionMode);
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


    constructor (address /* payable */ _owner) 
        public
    {
        mode = AuctionMode.NeverStarted;
        owner = _owner;
    }
    
    function openAuction(uint _closingTime) 
        public
        inMode(AuctionMode.NeverStarted)
        by(owner)
    {
        require (_closingTime > now);

        mode = AuctionMode.Open;
        closingTime = _closingTime;

        this.value = 0;
        this.bidder = owner;
    }
    
    /*@ succeeds_only_if
      @   mode == AuctionMode.Open, // inMode(AuctionMode.Open) 
      @   msg.sender != owner,      // notBy(owner)
      @   msg.value > this.value,
      @   now <= closingTime;
      @ after_success
      @   this.value > \old(this.value),
      @   let effective_net(a) be net(a) - withdrawableBalances[a]
      @   in
      @     effective_net(this.bidder) == msg.value, //even if this.bidder is \old(this.bidder)
      @     \old(this.bidder) != msg.sender ==> effective_net(\old(this.bidder)) == 0;
      @*/
    function makeBid()
        public
        /* payable */
        inMode(AuctionMode.Open) 
        notBy(owner)
    {
        require (msg.value > this.value);
        require (now <= closingTime);
        
        // Update withdrawable balances
        withdrawableBalances[this.bidder] = withdrawableBalances[this.bidder] + this.value;
        
        // Remember the new bid
        this.value = msg.value;
        this.bidder = msg.sender;
    }    
    
    /*@ succeeds_only_if
      @   msg.sender == owner || msg.sender == this.bidder,
      @   now > closingTime;
      @ after_success
      @   let effective_net(a) be net(a) - withdrawableBalances[a]
      @   in
      @   effective_net(owner) == -net(this.bidder);
      @*/
    function closeAuction() 
        public
        inMode(AuctionMode.Open) // reasonable assumtion, but makes locking of funds more likely
    {
        require (
            msg.sender == owner || 
            msg.sender == this.bidder
        );
        require (now > closingTime);
        
        mode = AuctionMode.Closed;
        withdrawableBalances[owner] += this.value;
    }

    /*@ after_success
      @   withdrawableBalances[msg.sender] == 0,
      @   net(msg.sender) == \old( net(msg.sender) + withdrawableBalances[msg.sender] );
      @*/
    function withdraw() 
        public
    {
        uint tmp = withdrawableBalances[msg.sender];
        withdrawableBalances[msg.sender] = 0;
        msg.sender.transfer(tmp);
    }
}
