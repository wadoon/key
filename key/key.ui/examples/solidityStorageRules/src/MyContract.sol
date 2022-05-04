contract MyContract {

	struct B { uint b1; uint b2; }
	struct A { int a1; int a2; }
	
	A f;
	int i;
	
  function m() public {
	   //j[0] = 42;
	   //f.a2 = f.a1;
	   //this.f.a2.b2 = 42; // OK with      storage = Storage(A(B(c1, c2), B(c3, c4)), c5) -> \<{ self.m(msg)@MyContractImpl; }\> storage = Storage(A(B(c1, c2), B(c3, 42)), c5)
	   //this.i = 42; // OK with    storage = Storage(A(B(1, 2), B(3, 4)), 0) -> \<{ self.m(msg)@MyContractImpl; }\> self.i = 42
	   //int y = this.i;
	   //this.f.a1.b1 = 0;
	   //uint x = this.i; // OK
  }

}