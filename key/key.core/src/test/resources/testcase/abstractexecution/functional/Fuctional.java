public class Functional {
    // Provable
    /*@ public normal_behavior
      @ ensures \result == 1;
      @*/
    public int irrelevantAS() {
        int x = 1;
        
        /*@ assume \disjoint(\dl_frameP, \dl_singletonPV(\dl_PV(x))) &&
          @        \disjoint(\dl_frameP, \dl_singletonPV(\dl_PV(\dl_heap))); // Needed for class invariant 
          @*/
        { ; }
        
        /*@ assignable \dl_frameP;
          @ accessible \dl_footprintP;
          @
          @ return_behavior requires false;
          @ exceptional_behavior requires false;
          @*/
        \abstract_statement P;
        
        return x;
    }
    
    // Not provable
    /*@ public normal_behavior
      @ ensures \result == 1;
      @*/
    public int relevantAS() {
        int x = 1;
              
        /*@ assume //\dl_disjoint(\dl_frameP, \dl_singletonPV(\dl_PV(x))) && // <-- Crucial
          @        \dl_disjoint(\dl_frameP, \dl_singletonPV(\dl_PV(\dl_heap))); // Needed for class invariant 
          @*/
        { ; }
      
        /*@ assignable \dl_frameP;
          @ accessible \dl_footprintP;
          @
          @ return_behavior requires false;
          @ exceptional_behavior requires false;
          @*/
        \abstract_statement P;
      
        return x;
    }
}