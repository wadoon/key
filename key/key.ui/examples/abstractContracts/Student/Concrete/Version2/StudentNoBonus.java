class StudentRecord {

	// exam result
	int exam;
	
	// achieved bonus
	int bonus;
	
	// minimum grade necessary to pass the exam
	int passingGrade;
	
	// completed labs
	boolean[] labs = new boolean[10];
	
	//@ public invariant exam >= 0 && bonus >= 0 && passingGrade >= 0;
	//@ public invariant labs.length == 10;

    boolean bonusAccepted = false;
    /*@
    @ public normal_behavior
    @ requires bonus >= 0;
    @ ensures (exam >= passingGrade) 
    	==> \result == exam + bonus;
    @ ensures (exam < passingGrade) 
    	==> \result == exam;
    @ assignable bonusAccepted;
    @*/

    int computeGrade(){
        if (exam >= passingGrade) {
            return exam + bonus;
            bonusAccepted = true;
        } else {
            return exam;
	   bonusAccepted = false; 
        }}
	
	/*@
	@ public normal_behavior
	@ ensures \result ==> exam + bonus >= passingGrade;
	@ ensures \result ==> (\forall int x; 0 <= x && x < 10; labs[x]);
	@ assignable bonusAccepted;
	@*/
	boolean passed() {
		boolean enoughPoints = computeGrade() >= passingGrade;
		boolean allLabsDone = true;
		/*@ loop_invariant 0 <= i && i <= 10 
	    	&& (\forall int x; 0 <= x && x < i; allLabsDone ==> labs[x]);
	   	assignable allLabsDone;
	   	decreases 10 - i;
	  	@*/
		for (int i = 0; i < 10; i++) {
	 	   allLabsDone = allLabsDone && labs[i];
		}
		return enoughPoints && allLabsDone;
	}
}
