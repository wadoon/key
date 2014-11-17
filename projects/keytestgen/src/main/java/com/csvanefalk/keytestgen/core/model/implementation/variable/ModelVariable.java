package com.csvanefalk.keytestgen.core.model.implementation.variable;

import java.util.List;

import com.csvanefalk.keytestgen.StringConstants;
import com.csvanefalk.keytestgen.core.model.implementation.instance.ModelArrayInstance;
import com.csvanefalk.keytestgen.core.model.implementation.instance.ModelInstance;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Instances of this class represent Java program variables during runtime. It's
 * main function is to encapsulate a corresponding instance of
 * {@link ProgramVariable}, which will contain rather complete information about
 * the variable itself. However, it adds an additional layer of runtime
 * information, showing exactly which concrete object on the heap this variable
 * points to.
 * <p/>
 * Instances of this class can represent either an object reference or primitive
 * type reference.
 * <ul>
 * <li>If it represents an object reference, its bound value will be a
 * {@link com.csvanefalk.keytestgen.core.model.implementation.instance.ModelInstance}, representing the heap object this variable is pointing
 * to. This value defaults null if no reference is given.</li>
 * <li>If it represents a primitive reference, then its value be one of the
 * primitive wrapper classes supported by KeY ({@link Integer}, {@link Boolean},
 * {@link Long}, {@link Byte} or {@link Character}). It cannot be null in this
 * case.</li>
 * </ul>
 *
 * @author christopher
 */
public class ModelVariable {

    /**
     * The value bound to this object. Primitive types are represented by their
     * wrapper types ( {@link Integer}, {@link Boolean} etc).
     */
    private Object boundValue;

    /**
     * Represents a unique identifier for this variable, denoting its relative
     * point of declaration in the program, in the form
     * self_dot_someField_dot_someOtherField_dot_thisvariable. Since no two
     * variables can have the same declaration space, this is also used to
     * uniquely distinguish this variable as a unqiue identifer.
     */
    private final String identifier;

    /**
     * This flag indicates whether or not this variable is declared in the
     * parameter list for a method.
     */
    private boolean isParameter = false;

    /**
     * The instance of {@link com.csvanefalk.keytestgen.core.model.implementation.instance.ModelInstance} in which this particular instance
     * of {@link ModelVariable} has been initialized.
     */
    private ModelInstance parentModelInstance;

    /**
     * The wrapped {@link ProgramVariable} instance.
     */
    protected final IProgramVariable variable;

    public ModelVariable(final IProgramVariable programVariable, final String identifier) {

        variable = programVariable;
        this.identifier = identifier;
        
        arrayIdx = -1; //default that this model variable is not an array's element
        arrayIdxTerm = null;
    }
    
    public ModelVariable(final String identifier){
       this.identifier = identifier;
       this.variable = null;
       arrayIdx = -1;
       arrayIdxTerm = null;
    }

    /*
     * clone constructor (just create fresh boundValue)
     * */
    public ModelVariable(final ModelVariable mv){
       if(mv.isPrimitive()){
          if(mv.boundValue instanceof Number)
             this.boundValue = 0; //number type
          else
             this.boundValue = false; //boolean type
       }else
          this.boundValue = mv.boundValue;
       
       this.identifier = mv.identifier;
       this.isParameter = mv.isParameter;
       //this.parentModelInstance = mv.parentModelInstance;
       this.variable = mv.variable;
       this.symbolicValue = mv.symbolicValue;
       this.isStatic = mv.isStatic;
       this.declareClassName = mv.declareClassName;
       this.constraints = mv.constraints;
       this.arrayIdx = mv.arrayIdx;
       this.arrayIdxValue = mv.arrayIdxValue;
       this.parentIdentifier = mv.parentIdentifier;
       this.arrayIdxTerm = mv.arrayIdxTerm;
    }
    
    /*
     * added by Huy, used to store symbolic value of variable
     */
    private Term symbolicValue;
    
    /*
     * added by Huy, used to indicate the variable is static or nonstatic
     */
    private boolean isStatic;
    
    /*
     * added by Huy, used to store the name of the class in which variable is declared
     * used mostly for accessing static variables
     */       
    private String declareClassName;
    
    private List<Term> constraints; //contain all constraints of variable (added by Huy)
    
    private int arrayIdx; //=-1 if this is not an element of array, otherwise is the index number (added by Huy) 
    
    /*
     *added by Huy, store the value of position in the array if this ModelVariable object is an array element
     *otherwise, arrayIdxValue =  null
     * */
    private Object arrayIdxValue;
    private Term arrayIdxTerm;
    
    private String parentIdentifier; //used to store the name of parent object    
   
    /**
     * Since we are working with unique Java assertions, two
     * {@link ModelVariable} instances are equal iff. their paths are identical.
     */
    @Override
    public boolean equals(final Object obj) {

        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ModelVariable other = (ModelVariable) obj;
        return identifier.equals(other.identifier);
    }

    /**
     * A variable is uniquely identified by its identifier.
     */
    public String getIdentifier() {

        return identifier;
    }

    /**
     * Returns the {@link ModelInstance} of which this variable is a field
     *
     * @return
     */
    public ModelInstance getParentModelInstance() {

        return parentModelInstance;
    }

    public KeYJavaType getType() {
        return variable.getKeYJavaType();
    }

    public Sort getSort(){
       return variable.sort();
    }
    /**
     * Returns a String representation of the {@link KeYJavaType} of this
     * variable.
     */
    public String getTypeName() {
       try{
          return variable.getKeYJavaType().getName();
       }catch(Exception e){
          return variable.sort().toString();
       }
    }

    /**
     * Returns the value of the variable. Will have to be explicitly converted
     * based on the type of this variable.
     */
    public <T> T getValue() {

        return (T) boundValue;
    }

    public String getVariableName() {

        final String rawName = variable.name().toString();
        final int lastColon = rawName.lastIndexOf(':');

        if (lastColon != -1) {
            return rawName.substring(lastColon + 1);
        } else {
            return rawName;
        }
    }

    /**
     * @return the isParameter
     */
    public boolean isParameter() {
        return isParameter;
    }

    /**
     * @param isParameter the isParameter to set
     */
    public void setParameter(final boolean isParameter) {
        this.isParameter = isParameter;
    }

    /**
     * Sets the {@link ModelInstance} of which this variable forms a field.
     * FIXME: this should not be assignable at all, violates abstraction.
     *
     * @param parentModelInstance
     */
    public void setParentModelInstance(final ModelInstance parentModelInstance) {

        this.parentModelInstance = parentModelInstance;
    }

    /**
     * Sets the value of this variable. TODO: Add type checking?
     *
     * @param value
     */
    public void setValue(final Object value) {

        boundValue = value;
    }

   

   @Override
    public String toString() {
        return getTypeName() + " : " + identifier;
    }

    public boolean isPrimitive() {
        return boundValue instanceof Number || boundValue instanceof Boolean;
    }

   /**
    * @return the symbolicValue
    */
   public Term getSymbolicValue() {
      return symbolicValue;
   }

   /**
    * @param symbolicValue the symbolicValue to set
    */
   public void setSymbolicValue(Term symbolicValue) {
      this.symbolicValue = symbolicValue;
   }
    
   public boolean isStatic(){
      return isStatic;
   }
   
   public void setStatic(boolean is){
      isStatic = is;
   }
   
   public IProgramVariable getProgramVariable(){
      return variable;
   }

   /**
    * @return the declareClassName
    */
   public String getDeclareClassName() {
      return declareClassName;
   }

   /**
    * @param declareClassName the declareClassName to set
    */
   public void setDeclareClassName(String declareClassName) {
      this.declareClassName = declareClassName;
   }

   /**
    * @return the constraints
    */
   public List<Term> getConstraints() {
      return constraints;
   }

   /**
    * @param constraints the constraints to set
    */
   public void setConstraints(List<Term> constraints) {
      this.constraints = constraints;
   }

   /**
    * @return the arrayIdx
    */
   public int getArrayIdx() {
      return arrayIdx;
   }

   /**
    * @param arrayIdx the arrayIdx to set
    */
   public void setArrayIdx(int arrayIdx) {
      this.arrayIdx = arrayIdx;
   }
   
   public boolean isArrayElement(){
      //return (arrayIdx >= 0);
      if(arrayIdx>=0)
         return true;
      else         
         return (arrayIdxValue != null);
   }
   
   public boolean isArrayLength(){
      /*return ((getParentModelInstance() instanceof ModelArrayInstance) && (arrayIdx < 0)
            && identifier.endsWith(StringConstants.LENGTH));  */  
      return ((getParentModelInstance() instanceof ModelArrayInstance)
            && !isArrayElement()
            && identifier.endsWith(StringConstants.LENGTH));
   }
   
   /**
    * @return the arrayIdxValue
    */
   public <T> T getArrayIdxValue() {
      return (T) arrayIdxValue;
   }

   /**
    * @param arrayIdxValue the arrayIdxValue to set
    */
   public void setArrayIdxValue(Object arrayIdxValue) {
      this.arrayIdxValue = arrayIdxValue;
   }

   public String getParentIdentifier() {
      return parentIdentifier;
   }

   public void setParentIdentifier(String parentIdentifier) {
      this.parentIdentifier = parentIdentifier;
   }
   
   /*
    * return runtime type of variable
    * added by Huy
    */   
   public String getRuntimeType(){
      String runtimeType;
      if(symbolicValue!=null){
         if(!TermParserTools.isNullSort(symbolicValue)){
            runtimeType = symbolicValue.sort().toString();            
         }else{
            runtimeType = getTypeName();
         }
      }else{
         runtimeType = getTypeName();
      }
      return runtimeType;
   }

   public Term getArrayIdxTerm() {
      return arrayIdxTerm;
   }

   public void setArrayIdxTerm(Term arrayIdxTerm) {
      this.arrayIdxTerm = arrayIdxTerm;
   }
   
   
   
}