
public class HashTable {
    
	// Open addressing Hashtable with linear probing as collision resolution.
	
	/*@ public invariant 
	  @ h != null;
	  @*/
	
	/*@ public invariant 
	  @ \typeof(h) == \type(Object[]); 
	  @*/	 

	public /*@ spec_public nullable @*/ Object[] h;
	
	/*@ public invariant 
	  @ h.length == capacity;
	  @*/
	
	/*@ public invariant 
	  @ size >= 0 && size <= capacity;
	  @*/	
	public int size; 
	
	/*@ public invariant 
	  @ capacity >= 1;
	  @*/	
	public int capacity;
	
	HashTable (int capacity) {
		h = new Object[capacity]; 
		this.capacity = capacity;
		size = 0;
	}
	
	public static final boolean hashfun_ok = true;
	public static final boolean add_full = true;
	public static final boolean add_ok = true;
	
  /*@ 
    @ public normal_behaviour
    @ requires hashfun_ok && val > 0;
    @ ensures \result >= 0 && \result < capacity;
    @ assignable \nothing;
    @ diverges true;
    @*/
	private int hash_function (int val) {
        int result = 0;
        
		if (val >= 0)
		   result = val % capacity;
		else {result = (val * -1) % capacity;}
		
		return result;
	}
		
  /*@ 
    @ public normal_behaviour
    @ requires add_ok && size < capacity && key > 0;
    @ ensures ( \exists int i ;i >= 0 && i < capacity ;h[i]== u) ;
    @ assignable size, h[*];
    @ diverges true;
    @
    @ also
    @
    @ public normal_behaviour
    @ requires add_full && size >= capacity;
    @ ensures ( \forall int j ;j >= 0 && j < capacity ;h[j]== \old(h) [ j]);
    @ assignable \nothing;
    @ diverges true;
    @*/
	public void add (Object u, int key) {
        if (size < capacity) {
            int i = hash_function(key);

            if (h[i] == null) {
               h[i] = u;
               size++;
               return;
            }
            else {		
               int j = 0;
  
               while (h[i] != null && j < capacity) {
                     if (i == capacity-1) i = 0;
                     else {i++;}
               
                     j++; 
               }
 			
               h[i] = u;
               size++;
               return;			
            }	
         } else { return; }	
	}   

	// Removes an entry from the hashtable.
	public void delete (Object u, int key) {		
		int i = hash_function(key);
		int j = 0;

    	while (!u.equals(h[i]) && (j < capacity))
		    {            
			   if (i == capacity-1) i = 0;
	           else {i++;}
			   
			   j++;
		    }
    	
    	if (u.equals(h[i])){    		
    	    size = size - 1; 
    	    h[i] = null;
		}
	}
    
	// check if an intry is in hashtable. If it is, then returns the position in the hashtable where it is.
	// if it isn't, returns -1.
	public /*@ pure @*/ int contains (Object u, int key) {
		int i = hash_function(key);
		int j = 0;
		if (u == null) return -1;
		
		while (!u.equals(h[i]) && (j < capacity))
		{            
		   if (i == capacity-1) i = 0;
	       else {i++;}
	   
	       j++;
		}
		
        if (u.equals(h[i]))    		
   	       return i;		  
        else {return -1;}
	}
	
	// access to the entry of hashtable in the position idx.
	public Object get (int idx) {
		return h[idx];	
	}
}
