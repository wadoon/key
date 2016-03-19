/**
 * 
 */
package de.uka.ilkd.key.nui.util;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public final class NUIConstants {

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

    public final static String DEFAULT_XML_PATH = "resources/xml/cssList.xml";
    public final static String KEY_WINDOW_ICON = "file:resources/images/key-color-icon-square.png";

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
            + ".varSV{background-color:#9B30FF;color:#000000;font-weight:inherit;font-style:inherit;}"
            + ".warySubstOp{background-color:#2fedff;color:#FF0000;font-weight:inherit;font-style:italic;}";

    public static String getDefaultSequentCss() {
        return DEFAULT_SEQUENT_CSS;
    }

    /**
     * 
     */
    public NUIConstants() {
        // TODO Auto-generated constructor stub
    }

}