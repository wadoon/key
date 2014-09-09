package com.csvanefalk.keytestgen.core.model.implementation.variable;

import com.csvanefalk.keytestgen.core.model.implementation.instance.ModelArrayInstance;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * Created by christopher on 09/01/14.
 * <p/>
 * Represents a primitive Java array. Can hold either primitive or reference
 * type elements.
 */
public class ModelArrayVariable extends ModelVariable {

    public ModelArrayVariable(final IProgramVariable programVariable,
                       final String identifier) {
        super(programVariable, identifier);
    }
    
    /**
     * @override
     */
    public String getTypeName() {
        return variable.getKeYJavaType().getSort().toString();
    }
    
    /*
     * return array's dimension 
     * based on analyzing sort string
     **/
    public int dimension(){
       /*ModelVariable mv = ((ModelArrayInstance)getValue()).getArrayElements().get(0);
       if(mv!=null){
          if(mv instanceof ModelArrayVariable)
             return ((ModelArrayVariable)mv).dimension() + 1;
          else
             return 1;
       }
       return 0;*/
       String sort = getSort().toString();
       int dimension = 0;
       while(sort.contains("[]")){
          dimension += 1;
          sort = sort.substring(sort.indexOf("[]")+2);
       }
       return dimension;
    }
}