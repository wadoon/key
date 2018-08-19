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

package de.uka.ilkd.key.smt.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Represents an object inside a heap.
 *
 * @author mihai
 *
 */
public class ObjectVal {
    /**
     * The name of the object.
     */
    private String name;
    /**
     * The length of the object.
     */
    private int length;
    /**
     * The sort of the object.
     */
    private Sort sort;
    /**
     * True if object is an exact instance of its sort.
     */
    private boolean exactInstance;
    /**
     * Maps field names to field values.
     */
    private Map<String, String> fieldvalues;
    /**
     * Maps array fields to array values.
     */
    private Map<Integer, String> arrayValues;

    /**
     * Maps function names to function values. Supported functions are model
     * fields and class invariant.
     */
    private Map<String, String> funValues;

    /**
     * creates a new object value of the given name
     * @param name the Object's name
     */
    public ObjectVal(String name) {
        this.name = name;
        fieldvalues = new HashMap<String, String>();
        arrayValues = new HashMap<Integer, String>();
        funValues = new HashMap<String, String>();
    }

    /**
     * associate the function name with the given value
     * @param fun the name of the function
     * @param val the value to be associated with the specified function
     */
    public void putFunValue(String fun, String val) {
        funValues.put(fun, val);
    }

    /**
     * set the i-th array element to the given value
     * @param i the array index
     * @param val the value
     */
    public void setArrayValue(int i, String val) {
        arrayValues.put(i, val);
    }

    /**
     * returns the i-th array element
     * @param i the index of the array element to be returned
     * @return the value stores at index i
     */
    public String getArrayValue(int i) {
        return arrayValues.get(i);
    }

    /**
     * sets the (exact) dynamic type of this object
     * @param exactInstance
     *            the exactInstance to set
     */
    public void setExactInstance(boolean exactInstance) {
        this.exactInstance = exactInstance;
    }

    /**
     * queries whether the (exact) dynamic type of this object is known
     * @return
     */
    public boolean isExactInstance() {
        return exactInstance;
    }

    /**
     * returns all values stored in this array
     * @return map associating an index with the value stored at that index
     */
    public Map<Integer, String> getArrayValues() {
        return arrayValues;
    }

    /**
     * returns the associated values for the given function names
     * @return map of function name to associated value
     */
    public Map<String, String> getFunValues() {
        return funValues;
    }

    /**
     * sets the name of this entity
     * @param name the name
     */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * queries the name of this entity
     * @return the name
     */
    public String getName() {
        return name;
    }


    /**
     * queries the sort of this entity
     * @return the sort
     */
    public Sort getSort() {
        return sort;
    }

    /**
     * sets the sort of this object/array/function
     * @param sort the sort
     */
    public void setSort(Sort sort) {
        this.sort = sort;
    }

    /**
     * returns the length of this array
     * @return the length
     */
    public int getLength() {
        return length;
    }

    /**
     * sets the length of this array
     * @param length the length
     */
    public void setLength(int length) {
        this.length = length;
    }

    /**
     * @return the fieldvalues
     */
    public Map<String, String> getFieldvalues() {
        return fieldvalues;
    }

    /**
     * @param fieldvalues
     *            the fieldvalues to set
     */
    public void setFieldvalues(Map<String, String> fieldvalues) {
        this.fieldvalues = fieldvalues;
    }

    /**
     * returns the currently associated valut to the specified field
     * @param field the field name
     * @return the value associated to the field (or null if no value is known)
     */
    public String get(String field) {
        // System.out.println(fieldvalues.keySet());
        return fieldvalues.get(field);
    }

    /**
     * associated a field to the given value
     * @param field the field
     * @param value the value assigned to the specified field
     * @return the old value of the field (or null if no value was known before)
     */
    public String put(String field, String value) {
        return fieldvalues.put(field, value);
    }

    /**
     * the value of the field specified by its short name
     * @param name the short name of the field
     * @return the value associated to the field (or null if not known)
     */
    public String getFieldUsingSimpleName(String name) {
        if (fieldvalues.containsKey(name)) {
            return fieldvalues.get(name);
        } else {
            for (final String field : fieldvalues.keySet()) {
                if (field.endsWith(name) ||
                        field.endsWith(name + "|")) {
                    return fieldvalues.get(field);
                }
            }
        }
        return null;
    }

    @Override
    /**
     * textual representation of this object
     * @return the string representation of this object
     */
    public String toString() {
        final String tab = "   ";

        // for null we don't care about length, type, etc.
        if (name.startsWith("#o0")) {
            return tab + "Object " + name + "\n";
        }

        final String type = sort == null ? "java.lang.Object"
                : sort.name().toString();

        String result = tab + "Object " + name + "\n";

        result += tab + tab + "length = " + length + "\n";
        result += tab + tab + "type =" + type + "\n";
        result += tab + tab + "exactInstance =" + this.exactInstance + "\n";
        // result += tab+tab+"<inv> = "+this.inv+"\n";

        final List<String> fields = new LinkedList<String>();
        fields.addAll(fieldvalues.keySet());
        Collections.sort(fields);

        for (final String field : fields) {
            result += tab + tab + field + " = " + fieldvalues.get(field);
            result += "\n";
        }

        for (final String fun : funValues.keySet()) {
            result += tab + tab + fun + " = " + funValues.get(fun);
            result += "\n";
        }

        final List<Integer> arrfields = new ArrayList<Integer>();
        arrfields.addAll(arrayValues.keySet());
        Collections.sort(arrfields);

        for (final int i : arrfields) {
            result += tab + tab + "[" + i + "] = " + arrayValues.get(i);
            result += "\n";
        }
        return result;
    }

    /**
     * Objects with equal names are equal.
     * @param o the Object to be compared to
     * @return true if this object and o have
     *   equal names
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof ObjectVal) {
            final ObjectVal ov = (ObjectVal) o;
            if (ov.name == null) {
                return name == null;
            }
            return ov.name.equals(name);
        }
        return false;
    }

    /**
     * sets a set of values stored at the indexes of this arrays
     * @param newArrayValues the map associated an array element to its value
     */
    public void setArrayValues(Map<Integer, String> newArrayValues) {
        this.arrayValues = newArrayValues;
    }

    /**
     * sets a set of values to be associated with the given function names
     * @param newArrayValues the map associated function names to their respective value
     */
    public void setFunValues(Map<String, String> newFunValues) {
        this.funValues = newFunValues;
    }
}