class Student{
	
	// exam result
	int exam;
	
	// minimum grade necessary to pass the exam
	int passingGrade;
	
	// completed labs
	boolean[] labs = new boolean[10];
	
	//@ public invariant exam >= 0 && passingGrade >= 0;
	//@ public invariant labs.length == 10;
	
	/*@
	@ public normal_behavior
	@ requires_abs computeGradeR; 
	@ ensures_abs computeGradeE;
	@ assignable_abs computeGradeA;
	@ def computeGradeR = true;
	@ def computeGradeE = \result == exam;
	@ def computeGradeA = \nothing;
	@*/
	int computeGrade(){
		return exam;
	}
	
	/*@
	public normal_behaviour
	@requires_abs passedR;
	@ensures_abs passedE1;
	@ensures_abs passedE2;
	@assignable_abs passedA;
	@def passedR = true;
	@def passedE1 = \result ==> exam >= passingGrade;
	@def passedE2 = \result ==> (\forall int x; 0 <= x && x < 10; labs[x]); 
	@def passedA = \nothing;
	@*/
	boolean passed(){
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
