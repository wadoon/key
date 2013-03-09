package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.keyabs.abs.ABSModificationVisitor;
import de.uka.ilkd.keyabs.abs.ABSVariableDeclarationStatement;

public class ABSProgVarReplacer extends ABSModificationVisitor {

    // indicates if ALL program variables are to be replace by new
    // variables with the same name
    protected boolean replaceallbynew=true;


    /**
     * stores the program variables to be replaced as keys and the new
     * program variables as values
     */
    protected Map<ProgramVariable, ProgramVariable> replaceMap;


    /**
     * creates a visitor that replaces the program variables in the given
     * statement by new ones with the same name
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     */
    public ABSProgVarReplacer(ProgramElement st, Map<ProgramVariable, ProgramVariable> map) {
        super(st);
        this.replaceMap = map;
    }


    /**
     * creates a visitor that replaces the program variables in the given
     * statement
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param replaceall decides if all variables are to be replaced
     */
    public ABSProgVarReplacer(ProgramElement st, 
            Map<ProgramVariable, ProgramVariable> map, 
            boolean replaceall) {
        this(st, map);
        this.replaceallbynew = replaceall;
    }


    //%%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static ProgramVariable copy(ProgramVariable pv) {
        return copy(pv, "");
    }


    //%%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static ProgramVariable copy(ProgramVariable pv, String postFix) {
        ProgramElementName name = pv.getProgramElementName();
        //%%% HACK: final local variables are not renamed since they can occur in an
        // anonymous class declared in their scope of visibility.
        /*      if(pv.isFinal()){
             return pv;
         }*/
        return new LocationVariable
                (VariableNamer.parseName(name.toString() + postFix,
                        name.getCreationInfo()),
                        pv.getKeYJavaType(), pv.isFinal());
    }


    protected void walk(ProgramElement node) {
        if (node instanceof ABSVariableDeclarationStatement && replaceallbynew) {
            ABSVariableDeclarationStatement vd= (ABSVariableDeclarationStatement)node;
            ProgramVariable pv = (ProgramVariable) vd.getVariable();
            if (!replaceMap.containsKey(pv)) {
                replaceMap.put(pv, copy(pv));
            }
        }
        super.walk(node);
    }


    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }

    public void performActionOnProgramVariable(ProgramVariable pv) {
        ProgramElement newPV = replaceMap.get(pv);
        System.out.println(pv + "---->" + newPV);
        if (newPV != null) {
            addNewChild(newPV);
        } else {
            addChild(pv);
        }
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }


}
