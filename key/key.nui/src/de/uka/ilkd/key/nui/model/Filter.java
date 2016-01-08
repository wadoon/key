package de.uka.ilkd.key.nui.model;

public class Filter {

    private String name;
    public String getName() {
        return name;
    }
    public void setName(String value) {
        name = value;
    }

    private String searchString;
    public String getSearchString() {
        return searchString;
    }
    public void setSearchString(String value) {
        searchString = value;
    }
    
    private boolean revert;
    public boolean getRevert(){
        return revert;
    }
    public void setRever(boolean value){
        revert = value;
    }
    
    private int before;
    public int getBefore(){
        return before;
    }
    public void setBefore(int value){
        before = value;
    }
    
    private int after;
    public int getAfter(){
        return after;
    }
    public void setAfter(int value){
        after = value;
    }

    public Filter() {
        reset();
    }

    public void reset() {
        revert = false;
        searchString = null;
        before = 2;
        after = 2;
    }

    public Filter Clone() {
        Filter filter = new Filter();
        filter.setName(this.name);
        filter.setSearchString(this.searchString);
        filter.setRever(this.revert);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        return filter;
    }
}
