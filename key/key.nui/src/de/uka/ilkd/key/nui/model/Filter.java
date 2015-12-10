package de.uka.ilkd.key.nui.model;

public class Filter {
    
    private String searchString;
    
    public String getSearchString(){
        return searchString;
    }
    
    public void setSearchString(String value){
        searchString = value;
    }
    
    private boolean useTerm;
    
    public boolean getUseTerm(){
        return useTerm;
    }
    
    public void setUseTerm(boolean value){
        useTerm = value;
    }
    
    public Filter(){
        reset();
    }
    
    public void reset(){
        useTerm = false;
        searchString = null;
    }
}
