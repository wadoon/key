// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.logic.JavaDLTerm;


public class AbbrevMap {
    
    /**
     * HashMaps used to store the mappings from JavaDLTerm to String, String to JavaDLTerm
     * and JavaDLTerm to Enabled. Enabled is set true if a abbreviation should be used when 
     * printing the term.
     */ 
    protected HashMap<AbbrevWrapper, String> termstring;
    protected HashMap<String, AbbrevWrapper> stringterm;
    protected HashMap<AbbrevWrapper, Boolean> termenabled;

    /**
     * Creates a  AbbrevMap.
     */
    public AbbrevMap() {
	termstring = new LinkedHashMap<AbbrevWrapper, String>();
	stringterm = new LinkedHashMap<String, AbbrevWrapper>();
	termenabled = new LinkedHashMap<AbbrevWrapper, Boolean>();
    }
       
    /**
     * Associates a JavaDLTerm and its abbreviation in this map.
     * @param t a term
     * @param abbreviation the abbreviation for of this term
     * @param enabled true if the abbreviation should be used 
     * (e.g. when printing the term), false otherwise.
     */ 
    public void put(JavaDLTerm t, String abbreviation, boolean enabled) 
	throws AbbrevException{
	AbbrevWrapper scw;
	if(containsTerm(t)){ 
	    throw new AbbrevException("A abbreviation for "+t+" already exists",
					true);
	}
	if(containsAbbreviation(abbreviation)){
	    throw new AbbrevException("The abbreviation "+abbreviation+" is already"+
					" in use for: "+getTerm(abbreviation),false);
	}
	scw = new AbbrevWrapper(t); 
	termstring.put(scw, abbreviation);
	stringterm.put(abbreviation, scw);
	termenabled.put(scw, enabled? Boolean.TRUE : Boolean.FALSE);
    }

    /**
     * Changes the abbreviation of t to abbreviation. If the AbbrevMap doesn't 
     * contain t nothing happens.
     */
    public void changeAbbrev(JavaDLTerm t, String abbreviation)
	throws AbbrevException{
	if(containsTerm(t)){
	    AbbrevWrapper scw;
	    if(containsAbbreviation(abbreviation)){
		throw new AbbrevException("The abbreviation "+abbreviation+" is already"+
		" in use for: "+getTerm(abbreviation),false);
	    }
	    scw = new AbbrevWrapper(t);
	    stringterm.remove(termstring.get(scw));	   
	    termstring.put(scw,abbreviation);
	    stringterm.put(abbreviation,scw);
	}
    }

    /**
     * Returns true if the map contains the abbreviation s.
     */
    public boolean containsAbbreviation(String s){
	return stringterm.containsKey(s);
    }

    /**
     * Returns true if the map contains the term t.
     */
    public boolean containsTerm(JavaDLTerm t){
	return termstring.containsKey(new AbbrevWrapper(t));
    }

    /**
     * Returns the term which is mapped to the abbreviation s, null if no term
     * is mapped to the abbreviation.
     */
    public JavaDLTerm getTerm(String s){
	return stringterm.get(s).getTerm();
    }

    /**
     * Returns the abbreviation mapped to the term t. Returns null if no abbreviation
     * is mapped to t.
     */ 
    public String getAbbrev(JavaDLTerm t){
	return "@"+termstring.get(new AbbrevWrapper(t));
    }
    
    /**
     * Returns true if the mapping is enabled, which means that the abbreviation may
     * be used.
     */
    public boolean isEnabled(JavaDLTerm t){
	Boolean b=termenabled.get(new AbbrevWrapper(t));
	if(b!=null) return b.booleanValue();
	return false;
    }
    
    /**
     * Sets the mapping of the term t to its abbreviation enabled or disabled
     * @param t a JavaDLTerm
     * @param enabled true if the abbreviation of t may be used.
     */
    public void setEnabled(JavaDLTerm t, boolean enabled){
	termenabled.put(new AbbrevWrapper(t), enabled? Boolean.TRUE : Boolean.FALSE);
    }

    public static class AbbrevWrapper{

        private JavaDLTerm t;

        public AbbrevWrapper(JavaDLTerm t){
            this.t = t;
        }

        public int hashCode(){
            return t.hashCode();
        }

        public boolean equals(Object o){
            if(!(o instanceof AbbrevWrapper)) return false;
            AbbrevWrapper scw = (AbbrevWrapper) o;
            if(scw.getTerm()==t) return true;
            return t.equals(scw.getTerm());
        } 

        public JavaDLTerm getTerm(){
            return t;
        }
    }
}