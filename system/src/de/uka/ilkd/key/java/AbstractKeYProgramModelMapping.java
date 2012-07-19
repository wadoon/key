package de.uka.ilkd.key.java;

import java.util.HashMap;
import java.util.Set;

import de.uka.ilkd.key.util.Debug;

public abstract class AbstractKeYProgramModelMapping {

	/** have special classes been parsed in */
	protected boolean parsedSpecial = false;

	public abstract AbstractKeYProgramModelMapping copy();

	/** maps a  program element (or something similar, e.g. Type)
	* to the KeY-equivalent
	*/
	protected HashMap map;
	
	/** Maps a KeY program element to the Recoder-equivalent */
	protected HashMap revMap;

	protected AbstractKeYProgramModelMapping() {
    	this.map = new HashMap();
    	this.revMap = new HashMap();
	}

	protected AbstractKeYProgramModelMapping(HashMap map, HashMap revMap,
			boolean parsedSpecial) {
        this.map      = map;
        this.revMap   = revMap;
    	this.parsedSpecial = parsedSpecial;
	}

	/**
	* returns a matching ProgramElement (KeY) to a given
	* ProgramElement (Recoder)
	* @param pe a recoder.java.ProgramElement
	*/
	public ProgramElement toKeY(recoder.java.ProgramElement pe) {
	    return (ProgramElement)map.get(pe);
	}

	/**
	* returns a matching ModelElement (KeY) to a given recoder.ModelElement
	* @param pe a recoder.ModelElement
	*/
	public ModelElement toKeY(recoder.ModelElement pe) {
	    return (ModelElement)map.get(pe);
	}

	/**
	* returns the Recoder-equivalent to a given ProgramElement (KeY).
	* If there's no RecodeR equivalent to program element pe, an
	* assertion failure "Program Element <pe> not known" is emitted.
	* @param pe a JavaProgramElement
	*/
	public recoder.java.ProgramElement toRecoder(ProgramElement pe) {
	    Object res=revMap.get(pe);
	    Debug.assertTrue(res!=null, "Program Element not known", pe);
	    return (recoder.java.ProgramElement)res;
	}

	/**
	* returns the Recoder-equivalent to a given ModelElement (KeY).
	* If there's no Recoder-equivalent to the ModelElement pe a
	* debug message "Model Element <pe> not known" is printed.
	* @param pe a ModelElement
	*/
	public recoder.ModelElement toRecoder(ModelElement pe) {
	    Object res=revMap.get(pe);
	if (res==null) {
	    //System.out.println(revMap);
	}
	    Debug.assertTrue(res!=null, "Model Element not known", pe);	
	
	    return (recoder.ModelElement)res;
	}

	public void put(Object rec, Object key) {
	Object formerValue = map.put(rec, key);
	Debug.assertTrue(formerValue == null, 
			 "keyrecodermapping: duplicate registration of type:", key);
	revMap.put(key, rec);
	}

	public boolean mapped(Object rec) {
	return map.containsKey(rec);
	}

	public Set elemsKeY() {
	return revMap.keySet();
	}

	public Set elemsRec() {
	return map.keySet();
	}

	/**
	 * As long as we do not support lemmata we need the source code of
	 * some 'java.lang' classes. These are parsed in using method
	 * parseSpecial of {@link Recoder2KeY}. To avoid multiple readings
	 * this method indicates whether the special have been parsed in or
	 * not. 
	 * @return true if special classes have been parsed in
	 */
	public boolean parsedSpecial() {
	return parsedSpecial;
	}

	public int size() {
	return map.size();
	}

	/**
	 * As long as we do not support lemmata we need the source code of
	 * some 'java.lang' classes. These are parsed in using method
	 * parseSpecial of {@link Recoder2KeY}. To avoid multiple readings
	 * this method sets a flag whether the special have been parsed in or
	 * not
	 * @param b boolean indicating if the special classes have been
	 * parsed in
	 */
	public void parsedSpecial(boolean b) {
	parsedSpecial = b;
	}

}