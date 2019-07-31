  public class SimpleAuctionVul extends Address {

    public boolean auctionOpen = true;

    public int currentBid = 0;

    private Address auctionOwner;

    private Address currentBidder;
     
    public Auction(Message msg) { 
      auctionOwner = msg.sender;      
    }

    public void placeBid(Message msg) {
      require(msg.sender != auctionOwner);

      // The auction must still be open
      require (auctionOpen);
      
      // The new bid must be higher than the current one
      require (msg.value > currentBid);

      // Remember the new bidder
      Address oldBidder = currentBidder;
      int oldBid = currentBid;
      currentBidder = msg.sender;
      currentBid = msg.value;

      // Return the money to current bidder (if there is any)
      if (oldBid != 0) {
        oldBidder.transfer(oldBid);
      }
       
    }

    public void closeAuction(Message msg) {
      require (msg.sender == auctionOwner);

      auctionOwner.transfer(currentBid);
      currentBid = 0;
  }
  }
  