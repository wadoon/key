contract MyContract {

  uint f;

  function m() public {
  	   f = 5; 	   
  }

  function n() public {
  	   uint storage localSt = this.f; 	   
  }

}