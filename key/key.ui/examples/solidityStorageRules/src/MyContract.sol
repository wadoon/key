contract MyContract {

	struct B { int b1; int b2; }
	struct A { B a1; B a2; }
	
	A f;
	//int i;
	//int[] j;
	
  function m() public {
		//this.i = 0;
	   //int x;
	   //x = j[0];
	   //this.i = 42;
	   //j[0] = 3+3;
	   //f.a2 = f.a1;
	   //f.a2.b2 = 42;
  }
}