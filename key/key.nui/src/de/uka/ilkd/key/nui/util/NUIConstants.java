/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.util.HashMap;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public final class NUIConstants {

    private static HashMap<Class, String> classMap = new HashMap<>();
    private static HashMap<Class, Boolean> classEnabledMap = new HashMap<>();

    public final static String OPEN_TAG_BEGIN = "<span class=\"";
    public final static String OPEN_TAG_END = "\">";
    public final static String CLOSING_TAG = "</span>";

    public final static String MOUSE_TAG = "mouseover";
    public final static String HIGHLIGHTED_TAG = "highlighted";
    public final static String FILTER_MINIMIZED_TAG = "minimized";
    public final static String FILTER_COLLAPSED_TAG = "collapsed";
    public final static String RULE_APP_TAG = "ruleApp";
    public final static String IF_INST_TAG = "ifInst";
    public final static String IF_FORMULA_TAG = "ifFormula";
    public final static String SELECTION_TAG = "filterSelection";
    public final static String DEFAULT_STYLE_CSS = "resources/css/sequentStyle.css";
    public final static String CSS_RESET_TO_DEFAULT_PATH = "resources/css/sequentStyleDefault.css";

    static {
        // Defines if this AST Class shall be highlighted
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Equality.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Function.class, false);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.LocationVariable.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Junctor.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.LogicVariable.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Quantifier.class, true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.SortDependingFunction.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Modality.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ObserverFunction.class,
                true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.AbstractSortedOperator.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.AbstractSV.class, true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.AbstractTermTransformer.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ElementaryUpdate.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.FormulaSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.IfExThenElse.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.IfThenElse.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ModalOperatorSV.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramConstant.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramMethod.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramVariable.class,
                true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.SchemaVariableFactory.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.SkolemTermSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.SubstOp.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.TermLabelSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.TermSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Transformer.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.UpdateApplication.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.UpdateJunctor.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.UpdateSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.VariableSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.WarySubstOp.class, true);

        // Define Style Span for each Class
        classMap.put(de.uka.ilkd.key.logic.op.Equality.class, "equality");
        classMap.put(de.uka.ilkd.key.logic.op.Function.class, "function");
        classMap.put(de.uka.ilkd.key.logic.op.LocationVariable.class,
                "locationVar");
        classMap.put(de.uka.ilkd.key.logic.op.Junctor.class, "junctor");
        classMap.put(de.uka.ilkd.key.logic.op.LogicVariable.class, "logicVar");
        classMap.put(de.uka.ilkd.key.logic.op.Quantifier.class, "quantifier");
        classMap.put(de.uka.ilkd.key.logic.op.SortDependingFunction.class,
                "sortDepFunc");
        classMap.put(de.uka.ilkd.key.logic.op.Modality.class, "modality");
        classMap.put(de.uka.ilkd.key.logic.op.ObserverFunction.class,
                "observerFunc");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractSortedOperator.class,
                "abstractSortOp");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractSV.class, "abstractSV");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractTermTransformer.class,
                "abstractTermTransf");
        classMap.put(de.uka.ilkd.key.logic.op.ElementaryUpdate.class,
                "elemUpdate");
        classMap.put(de.uka.ilkd.key.logic.op.FormulaSV.class, "formulaSV");
        classMap.put(de.uka.ilkd.key.logic.op.IfExThenElse.class,
                "ifExThenElse");
        classMap.put(de.uka.ilkd.key.logic.op.IfThenElse.class, "ifThenElse");
        classMap.put(de.uka.ilkd.key.logic.op.ModalOperatorSV.class,
                "modalOpSV");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramConstant.class,
                "progConst");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramMethod.class, "progMeth");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramSV.class, "progSV");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramVariable.class, "progVar");
        classMap.put(de.uka.ilkd.key.logic.op.SchemaVariableFactory.class,
                "schemaVarFactory");
        classMap.put(de.uka.ilkd.key.logic.op.SkolemTermSV.class,
                "skolemTermSV");
        classMap.put(de.uka.ilkd.key.logic.op.SubstOp.class, "substOp");
        classMap.put(de.uka.ilkd.key.logic.op.TermLabelSV.class, "termLabelSV");
        classMap.put(de.uka.ilkd.key.logic.op.TermSV.class, "termSV");
        classMap.put(de.uka.ilkd.key.logic.op.Transformer.class, "transformer");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateApplication.class,
                "updateApp");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateJunctor.class,
                "updateJunc");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateSV.class, "updateSV");
        classMap.put(de.uka.ilkd.key.logic.op.VariableSV.class, "varSV");
        classMap.put(de.uka.ilkd.key.logic.op.WarySubstOp.class, "warySubstOp");
    }

    /**
     * 
     */
    public NUIConstants() {
        // TODO Auto-generated constructor stub
    }

    /**
     * fills the classMap with each class name and its styleClass tag
     */

    public static HashMap<Class, Boolean> getClassEnabledMap() {
        return classEnabledMap;
    }

    public static HashMap<Class, String> getClassCssMap() {
        return classMap;
    }

}
