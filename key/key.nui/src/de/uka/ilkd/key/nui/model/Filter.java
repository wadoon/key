package de.uka.ilkd.key.nui.model;

public class Filter {
    
    private String name;
    public String getName(){
        return name;
    }
    public void setName(String value){
        name = value;
    }
    
    private String searchString;
    
    public String getSearchString(){
        return searchString;
    }
    
    public void setSearchString(String value){
        searchString = value;
    }
    
    private String excludeString;
    
    public String getExcludeString(){
        return excludeString;
    }
    
    public void setExcludeString(String value){
        excludeString = value;
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
        excludeString = null;
    }
    
    public Filter Clone(){
        Filter filter = new Filter();
        filter.setName(this.name);
        filter.setSearchString(this.searchString);
        filter.setExcludeString(this.excludeString);
        filter.setUseTerm(this.useTerm);
        return filter;
    }
}
