contract MultiAuction {
  address /*payable*/ private auctionOwner;
  mapping (address => uint) public balances;
  mapping (address => bool) bidded;
  
  address /*payable*/[] public bidders;
  
  // The state of the contract
  enum State { AUCTION_OPEN, AUCTION_CLOSED }
  State private state;

    /*@ class_invariant
        (\exists address hb;
            (\forall address a;
                balances[hb] >= balances[a] &&
                (a != hb && a != auctionOwner -> balances[a] == net(a)) &&
                (state == State.AUCTION_OPEN -> net(auctionOwner) == 0) &&
                balances[hb] == net(hb) + net(auctionOwner)
            )
        ) &&
        (state == State.AUCTION_OPEN ->
            (\forall address a;
              (
                (net(a) > 0 -> bidded[a]==true) && ((\exists uint i; i>=0 && i< bidders.arr_length && bidders[i] == a) <-> (bidded[a]==true))
              )
            )
        ) &&
        !(\exists uint i; (i>=0 && i<bidders.arr_length && bidders[i]==auctionOwner)) &&
        balances[auctionOwner] == 0; 
    */

  /*@ on_success auctionOwner == msg.sender &&
                 state == State.AUCTION_OPEN; */
  constructor() public {
    auctionOwner = msg.sender;
    state = State.AUCTION_OPEN;
  }

  /*@ only_if state == State.AUCTION_OPEN &&
              msg.sender != auctionOwner &&
              msg.value > 0;
      on_success balances[msg.sender] == \old(balances[msg.sender]) + msg.value;
      assignable  balances[msg.sender], bidders[bidders.arr_length], bidders.arr_length, bidded[msg.sender], net(msg.sender);
  */
  function placeOrIncreaseBid() public payable {
    // Place or increase someone's bid

    require(state == State.AUCTION_OPEN);
    require(msg.sender != auctionOwner);
    require(msg.value > 0);

    balances[msg.sender] = balances[msg.sender] + msg.value;

    bool bid = bidded[msg.sender];
    if (!bid) {
//    if (!bidded[msg.sender]) {  does not work
      bidders.push(msg.sender);
      bidded[msg.sender] = true;
    }
  }

  /*@ only_if state == State.AUCTION_OPEN;
      on_success net(msg.sender) == 0;
      assignable balances[msg.sender],net(msg.sender);
   */
  function withdraw() public  {
    // A bidder can withdraw all her money (but she will stay in the array bidders)

    require(state == State.AUCTION_OPEN);

    uint tmp = balances[msg.sender];
    balances[msg.sender] = 0;
    msg.sender.transfer(tmp);
  }

  function closeAuction() public {

    // Only the auction owner can close the auction
    require(msg.sender == auctionOwner);
    require(state == State.AUCTION_OPEN);

    require(bidders.length > 0);

    state = State.AUCTION_CLOSED;

    uint i;

    address winner;
    uint highestBid = 0;

    // Get the winner and the highest bid
    for(i = 0; i < bidders.length; i = i + 1)
      if (balances[bidders[i]] > highestBid) {
        winner = bidders[i];
        highestBid = balances[winner];
      }

    // Transfer the money to the auction owner
    // balances[winner] = 0;

    auctionOwner.transfer(highestBid);

    // Reimburse everyone else
    for(i = 0; i < bidders.length; i = i + 1) {

      address /*payable*/ bidder = bidders[i];
      uint tmp = balances[bidder];
            
      if (bidder != winner && tmp != 0) {
        balances[bidder] = 0;
        bidder.transfer(tmp);
      }
    }
  }
}
