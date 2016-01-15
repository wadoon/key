package de.uka.ilkd.key.nui.model;

import java.util.Observable;

public class PrintFilter extends Observable {

    private String name;
    public String getName() {
        return name;
    }
    public void setName(String value) {
        name = value;
        // no need to notify observer since the name is only for storage
    }

    private String searchString;
    public String getSearchString() {
        return searchString;
    }
    public void setSearchString(String value) {
        if(searchString == value)return;
        searchString = value;
        notifyObservers();
    }
    
    private boolean invert;
    public boolean getInvert(){
        return invert;
    }
    public void setInvert(boolean value){
        if(invert == value) return;
        invert = value;
        notifyObservers();
    }
    
    private int before;
    public int getBefore(){
        return before;
    }
    public void setBefore(int value){
        if(value == before) return;
        before = value;
        notifyObservers();
    }
    
    private int after;
    public int getAfter(){
        return after;
    }
    public void setAfter(int value){
        if(after == value) return;
        after = value;
        notifyObservers();
    }
    
    private FilterMode filterMode;
    public FilterMode getFilterMode(){
        return filterMode;
    }
    public void setFilterMode(FilterMode value){
        if(filterMode == value) return;
        filterMode = value;
        notifyObservers();
    }

    public PrintFilter() {
        invert = false;
        searchString = null;
        before = 2;
        after = 2;
        filterMode = FilterMode.Minimize;
    }

    public PrintFilter Clone() {
        PrintFilter filter = new PrintFilter();
        filter.setName(this.name);
        filter.setSearchString(this.searchString);
        filter.setInvert(this.invert);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        filter.setFilterMode(this.filterMode);
        return filter;
    }
    
   public enum FilterMode {
        Collapse, Minimize
    }
}
