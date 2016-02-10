package de.uka.ilkd.key.nui.filter;

public final class EmptyEventArgs {

    private EmptyEventArgs(){
        
    }
    
    private static EmptyEventArgs args = new EmptyEventArgs();

    public static EmptyEventArgs get() {
        return args;
    }
}
