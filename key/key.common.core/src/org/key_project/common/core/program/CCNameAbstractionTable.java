package org.key_project.common.core.program;

public interface CCNameAbstractionTable<S> {

    /** 
     * adds the given two elements   to the table
     * @param p_e1 the first element  to be added
     * @param p_e2 the second element to be added     
     */
    void add(S p_e1, S p_e2);

    /** 
     * tests if the given elements have been assigned to the same
     * abstract name. 
     * @param p_e1 the first element 
     * @param p_e2 the second element 
     * @returns true if the pe1 and pe2 have been assigned to the same
     * name
     */
    boolean sameAbstractName(S p_e1, S p_e2);

}