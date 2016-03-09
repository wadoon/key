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

    private static HashMap<Class<? extends Object>, String> classMap = new HashMap<>();
    private static HashMap<Class<? extends Object>, Boolean> classEnabledMap = new HashMap<>();
    private static HashMap<String, String> classDescriptionMap = new HashMap<>();

    public final static String OPEN_TAG_BEGIN = "<span class=\"";
    public final static String OPEN_TAG_END = "\">";
    public final static String CLOSING_TAG = "</span>";

    public final static String MASTER_TAG = "pre";
    public final static String MOUSE_TAG = "mouseover";
    public final static String HIGHLIGHTED_TAG = "highlighted";
    public final static String FILTER_SELECTION_TAG = "filterSelection";
    public final static String FILTER_MINIMIZED_TAG = "minimized";
    public final static String FILTER_COLLAPSED_TAG = "collapsed";
    public final static String RULE_APP_TAG = "ruleApp";
    public final static String IF_INST_TAG = "ifInst";
    public final static String IF_FORMULA_TAG = "ifFormula";

    public final static String EQUALITY_TAG = "equality";
    public final static String FUNCTION_TAG = "function";
    public final static String LOCATIONVAR_TAG = "locationVar";
    public final static String JUNCTOR_TAG = "junctor";
    public final static String LOGICVAR_TAG = "logicVar";
    public final static String QUANTIFIER_TAG = "quantifier";
    public final static String SORTDEPFUNC_TAG = "sortDepFunc";
    public final static String MODALITY_TAG = "modality";
    public final static String OBSERVERFUNC_TAG = "observerFunc";
    public final static String ELEMUPDATE_TAG = "elemUpdate";
    public final static String FORMULASV_TAG = "formulaSV";
    public final static String IFEXTHENELSE_TAG = "ifExThenElse";
    public final static String IFTHENELSE_TAG = "ifThenElse";
    public final static String MODALOPSV_TAG = "modalOpSV";
    public final static String PROGCONST_TAG = "progConst";
    public final static String PROGMETH_TAG = "progMeth";
    public final static String PROGSV_TAG = "progSV";
    public final static String PROGVAR_TAG = "progVar";
    public final static String SCHEMAVARFACTORY_TAG = "schemaVarFactory";
    public final static String SKOLEMTERMSV_TAG = "skolemTermSV";
    public final static String SUBSTOP_TAG = "substOp";
    public final static String TERMLABELSV_TAG = "termLabelSV";
    public final static String TERMSV_TAG = "termSV";
    public final static String TRANSFORMER_TAG = "transformer";
    public final static String UPDATEAPP_TAG = "updateApp";
    public final static String UPDATEJUNC_TAG = "updateJunc";
    public final static String UPDATESV_TAG = "updateSV";
    public final static String VARSV_TAG = "varSV";
    public final static String WARYSUBSTOP_TAG = "warySubstOp";

    public final static String DEFAULT_STYLE_CSS_PATH = "resources/css/sequentStyle.css";
    public final static String CSS_RESET_TO_DEFAULT_PATH = "resources/css/sequentStyleDefault.css";

    public final static String DEFAULT_SEQUENT_CSS = "pre{background-color:#FFFFFF;color:#000000;font-weight:normal;font-size:16px;font-family:Courier New;font-style:normal;}"
            + ".highlighted{background-color:#FFFF00;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".mouseover{background-color:#B0C4DE;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".filterSelection{background-color:#ff6666;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".minimized{background-color:inherit;color:inherit;font-weight:inherit;font-size:6px;font-style:inherit;}"
            + ".collapsed{display:none;}.ruleApp{background-color:#B3FD53;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".ifInst{background-color:#ccffcc;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".ifFormula{background-color:#ccffcc;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".equality{background-color:inherit;color:#FF0000;font-weight:inherit;font-style:inherit;}"
            + ".function{background-color:inherit;color:#000000;font-weight:inherit;font-style:inherit;}"
            + ".locationVar{background-color:inherit;color:#0000FF;font-weight:bold;font-style:inherit;}"
            + ".junctor{background-color:inherit;color:#0000FF;font-weight:bold;font-style:italic;}"
            + ".logicVar{background-color:inherit;color:#008000;font-weight:inherit;font-style:inherit;}"
            + ".quantifier{background-color:inherit;color:#ff3300;font-weight:inherit;font-style:inherit;}"
            + ".sortDepFunc{background-color:inherit;color:#000000;font-weight:bold;font-style:inherit;}"
            + ".modality{background-color:inherit;color:inherit;font-weight:bold;font-style:inherit;}"
            + ".observerFunc{background-color:#008000;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".elemUpdate{background-color:inherit;color:#FFFF00;font-weight:bold;font-style:inherit;}"
            + ".formulaSV{background-color:#808080;color:#FFFF00;font-weight:inherit;font-style:inherit;}"
            + ".ifExThenElse{background-color:#008000;color:#FF0000;font-weight:bold;font-style:inherit;}"
            + ".ifThenElse{background-color:inherit;color:#008000;font-weight:bold;font-style:inherit;}"
            + ".modalOpSV{background-color:#0000FF;color:#FFFF00;font-weight:bold;font-style:inherit;}"
            + ".progConst{background-color:#000000;color:#FF0000;font-weight:bold;font-style:inherit;}"
            + ".progMeth{background-color:#000000;color:#008000;font-weight:bold;font-style:inherit;}"
            + ".progSV{background-color:#000000;color:#FFFFFF;font-weight:bold;font-style:inherit;}"
            + ".progVar{background-color:#000000;color:#2fedff;font-weight:bold;font-style:inherit;}"
            + ".schemaVarFactory{background-color:#003fff;color:#FF0000;font-weight:inherit;font-style:inherit;}"
            + ".skolemTermSV{background-color:#003fff;color:#FF00FF;font-weight:bold;font-style:inherit;}"
            + ".substOp{background-color:#808080;color:#FF0000;font-weight:inherit;font-style:inherit;}"
            + ".termLabelSV{background-color:#808080;color:#008000;font-weight:inherit;font-style:inherit;}"
            + ".termSV{background-color:#808080;color:#0000FF;font-weight:inherit;font-style:inherit;}"
            + ".transformer{background-color:#808080;color:#000000;font-weight:inherit;font-style:inherit;}"
            + ".updateApp{background-color:#FF00FF;color:inherit;font-weight:inherit;font-style:inherit;}"
            + ".updateJunc{background-color:#FF00FF;color:#008000;font-weight:inherit;font-style:inherit;}"
            + ".updateSV{background-color:#FF00FF;color:#0000FF;font-weight:bold;font-style:inherit;}"
            + ".varSV{background-color:violet;color:#000000;font-weight:inherit;font-style:inherit;}"
            + ".warySubstOp{background-color:#2fedff;color:#FF0000;font-weight:inherit;font-style:italic;}";

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
        classMap.put(de.uka.ilkd.key.logic.op.Equality.class, EQUALITY_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.Function.class, FUNCTION_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.LocationVariable.class,
                LOCATIONVAR_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.Junctor.class, JUNCTOR_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.LogicVariable.class,
                LOCATIONVAR_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.Quantifier.class, QUANTIFIER_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.SortDependingFunction.class,
                SORTDEPFUNC_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.Modality.class, MODALITY_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ObserverFunction.class,
                OBSERVERFUNC_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ElementaryUpdate.class,
                ELEMUPDATE_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.FormulaSV.class, FORMULASV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.IfExThenElse.class,
                IFEXTHENELSE_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.IfThenElse.class, IFTHENELSE_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ModalOperatorSV.class,
                MODALOPSV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ProgramConstant.class,
                PROGCONST_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ProgramMethod.class,
                PROGMETH_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ProgramSV.class, PROGSV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.ProgramVariable.class,
                PROGVAR_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.SchemaVariableFactory.class,
                SCHEMAVARFACTORY_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.SkolemTermSV.class,
                SKOLEMTERMSV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.SubstOp.class, SUBSTOP_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.TermLabelSV.class,
                TERMLABELSV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.TermSV.class, TERMSV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.Transformer.class,
                TRANSFORMER_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.UpdateApplication.class,
                UPDATEAPP_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.UpdateJunctor.class,
                UPDATEJUNC_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.UpdateSV.class, UPDATESV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.VariableSV.class, VARSV_TAG);
        classMap.put(de.uka.ilkd.key.logic.op.WarySubstOp.class,
                WARYSUBSTOP_TAG);

        classDescriptionMap.put(MASTER_TAG, "Basic Appearance");
        classDescriptionMap.put("." + HIGHLIGHTED_TAG, "Search Highlighting");
        classDescriptionMap.put("." + MOUSE_TAG, "Mouseover Highlighting");
        classDescriptionMap.put("." + FILTER_SELECTION_TAG,
                "Filter Mouse Selection Highlighing");
        classDescriptionMap.put("." + FILTER_MINIMIZED_TAG,
                "Filter: Minimization");
        classDescriptionMap.put("." + FILTER_COLLAPSED_TAG, "Filter: Hidden");
        classDescriptionMap.put("." + RULE_APP_TAG, "Last Applied Rule");
        classDescriptionMap.put("." + IF_INST_TAG, "Applied Rule Branch 1");
        classDescriptionMap.put("." + IF_FORMULA_TAG, "Applied Rule Branch 2");
        classDescriptionMap.put("." + EQUALITY_TAG, "Equality Term");
        classDescriptionMap.put("." + FUNCTION_TAG, "Function Term");
        classDescriptionMap.put("." + LOCATIONVAR_TAG, "Location Variable");
        classDescriptionMap.put("." + JUNCTOR_TAG, "Junctor");
        classDescriptionMap.put("." + LOGICVAR_TAG, "Logic Variable");
        classDescriptionMap.put("." + QUANTIFIER_TAG, "Quantifier");
        classDescriptionMap.put("." + SORTDEPFUNC_TAG,
                "Sort Depending Function");
        classDescriptionMap.put("." + MODALITY_TAG, "Modality Term");
        classDescriptionMap.put("." + OBSERVERFUNC_TAG, "Oberserver Function");
        classDescriptionMap.put("." + ELEMUPDATE_TAG, "Elementary Updater");
        classDescriptionMap.put("." + FORMULASV_TAG, "Formula Schema Variable");
        classDescriptionMap.put("." + IFEXTHENELSE_TAG,
                "If Ex then Else... Term");
        classDescriptionMap.put("." + IFTHENELSE_TAG, "If then Else... Term");
        classDescriptionMap.put("." + MODALOPSV_TAG,
                "Modal Operator Schema Variable");
        classDescriptionMap.put("." + PROGCONST_TAG, "Program Constants");
        classDescriptionMap.put("." + PROGMETH_TAG, "Program Method");
        classDescriptionMap.put("." + PROGSV_TAG, "Program Schema Variable");
        classDescriptionMap.put("." + PROGVAR_TAG, "Program Variable");
        classDescriptionMap.put("." + SCHEMAVARFACTORY_TAG,
                "Schema Variable Factory");
        classDescriptionMap.put("." + SKOLEMTERMSV_TAG,
                "Skolem Term Schema Variable");
        classDescriptionMap.put("." + SUBSTOP_TAG, "Substitution Operator");
        classDescriptionMap.put("." + TERMLABELSV_TAG,
                "Term Label Schema Variable");
        classDescriptionMap.put("." + TERMSV_TAG, "Term Schema Variable");
        classDescriptionMap.put("." + TRANSFORMER_TAG, "Transformer");
        classDescriptionMap.put("." + UPDATEAPP_TAG, "Update Application");
        classDescriptionMap.put("." + UPDATEJUNC_TAG, "Update Junctor");
        classDescriptionMap.put("." + UPDATESV_TAG, "Update Schema Variable");
        classDescriptionMap.put("." + VARSV_TAG, "Variable Schema Variable");
        classDescriptionMap.put("." + WARYSUBSTOP_TAG,
                "Wary Substition Operator");

    }

    /**
     * 
     */
    public NUIConstants() {
        // TODO Auto-generated constructor stub
    }

    public static HashMap<Class<? extends Object>, Boolean> getClassEnabledMap() {
        return classEnabledMap;
    }

    public static HashMap<Class<? extends Object>, String> getClassCssMap() {
        return classMap;
    }

    public static HashMap<String, String> getClassDescriptionMap() {
        return classDescriptionMap;
    }

}