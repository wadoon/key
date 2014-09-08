package com.csvanefalk.keytestgen.core.model.implementation;

import com.csvanefalk.keytestgen.core.model.implementation.instance.ModelArrayInstance;
import com.csvanefalk.keytestgen.core.model.implementation.instance.ModelInstance;
import com.csvanefalk.keytestgen.core.model.implementation.variable.ModelArrayVariable;
import com.csvanefalk.keytestgen.core.model.implementation.variable.ModelVariable;
import de.uka.ilkd.key.logic.Term;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * Represents an abstract heap state, consisting of {@link com.csvanefalk.keytestgen.core.model.implementation.variable.ModelVariable}
 * instances together with associated {@link com.csvanefalk.keytestgen.core.model.implementation.instance.ModelInstance} instances. See
 * separate documentation for both.
 *
 * @author christopher
 */
public class Model {

    public static final Model EMPTY_MODEL;

    static {
        EMPTY_MODEL = Model.constructModel();
    }

    /**
     * Factory method for creating a new {@link Model} instance.
     *
     * @return the new instance.
     */
    public static Model constructModel() {

        return new Model();
    }

    /**
     * Buffers variables which currently cannot be inserted due to broken
     * reference dependencies. Primarily, this will occur when the user tries to
     * insert a variable as a field into an instace which currently does'nt
     * exist. This can happens if this class is used in non-postorder
     * visitations of {@link Term} ASTs. Use mainly to allow safe visitations.
     */
    private final HashMap<ModelVariable, ModelVariable> buffer = new HashMap<ModelVariable, ModelVariable>();

    /**
     * The {@link ModelVariable} instances represented on this heap.
     */
    private final LinkedList<ModelVariable> variables = new LinkedList<ModelVariable>();

    private Model() {

    }

    /**
     * Adds a variable to the heap, causing it to point to a given object
     * instance. If the variable already exists on the heap, this method will
     * cause the variable to point to the new instance instead, unless the
     * variable is declared as <code>final</code>.
     *
     * @param variable the variable to be added
     * @param instance the instance the variable will point to. Can be
     *                 <code>null</code>.
     */
    public void add(final ModelVariable variable, final Object instance) {

        /*
         * TODO: This should throw an exception, not fail silently.

        if (!ModelVariable.isValidValueType(instance)) {
            return;
        }
        */

        /*
         * Check if the variable already exists in the buffer.
         */
        final ModelVariable localVariable = lookupVariable(variable);

        /*
         * If it does, configure it properly according to the provided value,
         * and proceed with adding it to the model.
         */
        if (localVariable == null) {

            variable.setValue(instance);

            if ((instance instanceof ModelInstance) && (instance != null)) {
                ((ModelInstance) instance).addReferee(variable);
            }

            variables.add(variable);

            /*
             * If it is not, then simply update the value currently pointed to
             * by the existing variable.
             */
        } else {

            if (instance instanceof ModelInstance) {
                ((ModelInstance) instance).addReferee(localVariable);
            }

            variable.setValue(instance);
        }
    }

    public void add(final ModelVariable variable) {
        add(variable, variable.getValue());
    }

    /**
     * Places the variable target as a field of the {@link ModelInstance}
     * referred to by the variable targetVariable.
     *
     * @param toBeInserted   the variable to insert as a field
     * @param targetVariable the variable pointing to the object instance we are inserting
     *                       into
     */
    public void assignField(ModelVariable toBeInserted, final ModelVariable targetVariable) {

        if (!toBeInserted.equals(targetVariable)) {
            toBeInserted = lookupVariable(toBeInserted);
            ModelVariable localOther = lookupVariable(targetVariable);

            if (localOther == null) {
                localOther = targetVariable;
            }

            /*
             * If the targetVariable currently does not exist in the Model, buffer it for
             * subsequent insertion.
             */
            if (targetVariable == null) {
                buffer.put(targetVariable, toBeInserted);
                return;
            }

            final ModelInstance instance = (ModelInstance) localOther.getValue();
            instance.addField(toBeInserted);
            toBeInserted.setParentModelInstance(instance);
        }
    }

    /**
     * Links two {@link ModelVariable} instances, causing target to point to the
     * {@link ModelInstance} which other is pointing to.
     *
     * @param target the target variable, i.e. the one the address of the instance
     *               is being bound to. Cannot be <code>null</code>
     * @param other  the other variable, i.e. the one currently holding the address
     *               of the instance. Cannot be <code>null</code>
     */
    public void assignPointer(ModelVariable target, ModelVariable other) {

        if (!target.equals(other)) {
            target = lookupVariable(target);
            other = lookupVariable(other);

            if (other != null) {
                target.setValue(other.getValue());
            } else {
                target.setValue(null);
            }
        }
    }

    /**
     * Returns the {@link ModelVariable} instance having a specific reference.
     *
     * @param reference the reference
     * @return the found instance, null if no instance is found with the
     * specified reference
     */
    public ModelVariable getVariable(final String reference) {

        for (final ModelVariable variable : variables) {

            if (variable.getIdentifier().equals(reference)) {
                return variable;
            }
        }
        return null;
    }

    /**
     * Gets all the {@link ModelVariable} instances defined in this model.
     *
     * @return
     */
    public final List<ModelVariable> getVariables() {

        return variables;
    }

    /**
     * Retrieves the actual in-memory reference to a variable, as represented on
     * the heap.
     *
     * @param variable the variable to lookup
     */
    private ModelVariable lookupVariable(final ModelVariable variable) {

        final int index = variables.indexOf(variable);
        return index >= 0 ? variables.get(index) : null;
    }
    
    
    /**
     * for printing purpose
     * */
    public String toString(){   
       String result = "";
       for(ModelVariable mv : getVariables()){      
          
          if(mv.isPrimitive()){
             result += mv.getIdentifier()+": " + mv.getSymbolicValue() + " :: " + mv.getTypeName()+ " : " + mv.getValue() + "\n" ;             
          }else if(mv instanceof ModelArrayVariable){
             result += mv.getIdentifier() + ": " + mv.getTypeName() + "; length: " +
                        ((ModelArrayInstance)mv.getValue()).length() + "; includes: \n";
             for(ModelVariable mvv : ((ModelArrayInstance)mv.getValue()).getArrayElements()){
                result += "     " + mvv.getIdentifier()+" : " + mvv.getVariableName()+" : " + mvv.getValue() + "; type: " + mvv.getSort().toString() + "\n";
             }
             result += "-----\n";
          }else{
             result += mv.getIdentifier()+": " + mv.getSymbolicValue() + " :: " ;
             ModelInstance mi=(ModelInstance)mv.getValue();
             result += mi.toString() + " ; " + " includes: \n";
             for(ModelVariable mvv : mi.getFields()){
                result += "     " + mvv.getIdentifier()+" : " + mvv.getVariableName()+" : " + mvv.getValue() + "; type: " + mvv.getSort().toString() + "\n";
             }
             result += "-----\n";
          }
       }       
       return result;      
    }
    
   /**
   * check if a ModelVariable is added into Model or not, use the identifier of var
   * @param identifier
   * @return true if there exists an ModelVariable mv that mv.identifier = identifier
   */
    public boolean inModel(String identifier){           
       if (getVariable(identifier) != null) 
          return true;
       else
          return false;
    }
    
    /** merge this model with another Model     
     * @param dModel
     * if there exists a ModelVariable of Model dModel that is not in this model
     * then add it into this model
     */
    public void mergeModel(Model dModel){
       List<ModelVariable> dMVs = dModel.getVariables(); 
       for(ModelVariable mv: dMVs){
          if(!inModel(mv.getIdentifier())){
             add(mv);
             //look up the referee
             List<ModelVariable> referees;
             try{
                referees = mv.getParentModelInstance().getReferees();
             }catch(Exception e){
                referees = null;
             }
             
             if(referees!=null){
                for(ModelVariable rmv: referees){
                   if(inModel(rmv.getIdentifier()))
                      assignField(mv, getVariable(rmv.getIdentifier()));                      

                }
             }
          }
       }
    }
    
    public void resetPrimitiveValue(){
       for(ModelVariable mv: getVariables()){
          if(mv.isPrimitive()){
             mv.setValue(ModelBuilderVisitor.resolvePrimitiveType(mv.getProgramVariable()));
          }
       }       
    }
}
