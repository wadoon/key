package de.uka.ilkd.key.nui.model;

import java.util.Observable;

public class Filter extends Observable {

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
    
    private boolean revert;
    public boolean getRevert(){
        return revert;
    }
    public void setRevert(boolean value){
        if(revert == value) return;
        revert = value;
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

    public Filter() {
        revert = false;
        searchString = null;
        before = 2;
        after = 2;
    }

    public Filter Clone() {
        Filter filter = new Filter();
        filter.setName(this.name);
        filter.setSearchString(this.searchString);
        filter.setRevert(this.revert);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        return filter;
    }
}
