package de.uka.ilkd.key.logic;

public class Placeholder extends Name {
    public final static int REQUIRES = 0;
    public final static int ENSURES = 1;
    public final static int ASSIGNABLE = 2;
    
    private final int type;
	
	public Placeholder(String n, int type) {
		super(n);
		this.type = type;
	}
	
	public int getType() {
		return type;
	}

}
