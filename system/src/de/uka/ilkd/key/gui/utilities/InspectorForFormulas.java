package de.uka.ilkd.key.gui.utilities;

import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.DefaultProofFileParser;

/**
 * Inspects whether a given string can be translated into a formula. 
 */
public class InspectorForFormulas implements CheckedUserInputInspector{

    private final IServices services;

    
    
    
    public InspectorForFormulas(IServices services) {
        super();
        this.services = services;
    }



    @Override
    public String check(String toBeChecked) {
        if(toBeChecked.isEmpty()){
            return CheckedUserInputInspector.NO_USER_INPUT;
        }
        Term term = translate(services,toBeChecked);
         
       if(term == null){
           return NO_USER_INPUT;
       }
       
       if(term.sort() != Sort.FORMULA){
           return "Not a formula.";
       }
       return null;

    }
    
    public static Term translate(IServices services, String toBeChecked){       
        return DefaultProofFileParser.parseTerm(toBeChecked, services, services.getNamespaces().variables(), 
                services.getNamespaces().programVariables());
    }

}