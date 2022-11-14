


public class ArrayList {

    //@ public invariant elementData != null;
	//@ public invariant \typeof(elementData) == \type(SimpleObject[]);
    public /*@ spec_public nullable @*/ SimpleObject[] elementData; 

    /*@ public normal_behavior
	  @ requires start < end;
	  @ requires start >= 0 && start < elementData.length;
	  @ requires end >= 0 && end <= elementData.length;
	  @ requires (\exists int i; i >= start && i < end;
	  @           ((o == null && elementData[i] == null) ||
	  @            (o != null && o.equals(elementData[i]))) );
	  @ assignable \nothing;
	  @ ensures (\exists int i; i >= start && i < end; 
	  @           ((o == null && elementData[i] == null) ||
	  @            (o != null && o.equals(elementData[i]))) && 
	  @          \result == i);
	  @
	  @ also
	  @
	  @ public normal_behavior
	  @ requires start < end;
	  @ requires start >= 0 && start < elementData.length;
	  @ requires end >= 0 && end <= elementData.length;
	  @ requires (\forall int i; i >= start && i < end;
	  @           ((o == null && elementData[i] != null) ||
	  @            (o != null && !o.equals(elementData[i]))));
	  @ assignable \nothing;
	  @ ensures \result == -1;
	  @ 
	  @ also
	  @
	  @ public normal_behavior
	  @ requires end >= 0 && end <= start && start < elementData.length;
	  @ assignable \nothing;
	  @ ensures \result == -1;
	  @
	  @ also
	  @
	  @ public exceptional_behavior
	  @ requires (start < 0 && start < end) || 
	  @          (start >= elementData.length && start < end) ||
	  @          (start >= 0 && start < elementData.length && start < end &&
	  @           end > elementData.length &&
	  @      (\forall int i; i >= start && i < elementData.length; 
	  @         ((o == null && elementData[i] != null) ||
	  @          (o != null && !o.equals(elementData[i])))));
	  @ assignable \nothing;
	  @ signals_only ArrayIndexOutOfBoundsException;
	  @ signals (ArrayIndexOutOfBoundsException) true;
	  @
	  @*/
    int indexOfRange(/*@ nullable @*/ SimpleObject o, int start, int end) {
		
        if (o == null) {
			/*@ loop_invariant
              @  (i >= start && start >= 0 && start < elementData.length && 
			  @   i <= elementData.length &&
			  @   (\forall int j; j >= start && j < i; elementData[j] != null)) ||
			  @  (start < 0 && i == start) ||
			  @  (start >= elementData.length && i == start);
              @ assignable \nothing;
              @ decreases elementData.length - i;
              @*/
            for (int i = start; i < end; i++) {
                if (elementData[i] == null) {
                    return i;
                }
            }
        } else {
			/*@ loop_invariant
              @  (i >= start && start >= 0 && start < elementData.length && 
			  @   i <= elementData.length &&
			  @   (\forall int j; j >= start && j < i; !o.equals(elementData[j]))) ||
			  @  (start < 0 && i == start) ||
			  @  (start >= elementData.length && i == start);
              @ assignable \nothing;
              @ decreases elementData.length - i;
              @*/
            for (int i = start; i < end; i++) {
                if (o.equals(elementData[i])) {
                    return i;
                }
            }
        }
        return -1;
    }
	
}


final class SimpleObject {
	
	private /*@ spec_public @*/ int id;
	
	/*@ public normal_behavior
	  @ ensures id >= 0 && id < 1000;
	  @*/
	public SimpleObject() {
		
	}
	
	/*@ public normal_behavior
	  @ requires o instanceof SimpleObject;
	  @ assignable \nothing;
	  @ ensures \result == (id == ((SimpleObject)o).id);
	  @
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires o == null;
	  @ assignable \nothing;
	  @ ensures \result == false;
	  @*/
	public final boolean /*@ pure @*/ equals(/*@ nullable @*/ Object o){
		if(o instanceof SimpleObject){
			return id == ((SimpleObject)o).id;
		}else{
			return false;
		}
	}
	
	
}