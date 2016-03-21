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

    public final static String CSSSTYLER_COLOR_TT_TEXT = "Pick a Color";
    public final static String CSSSTYLER_WEIGHT_TT_TEXT = "Choose the Boldness";
    public final static String CSSSTYLER_STYLE_TT_TEXT = "Turn Italics on/off";
    public final static String CSSSTYLER_SIZE_TT_TEXT = "Choose the Font Size";
    public final static String CSSSTYLER_FONT_TT_TEXT = "Choose a Font.\n"
            + "The SequentView might not be able to render every Font.\n"
            + "This is due to WebBrowser Compability.";
    public final static String CSSSTYLER_OTHER_TT_TEMPLATE = "Edit ";
    public final static String CSSSTYLER_INHERITED_TT_TEMPLATE = "If this checkbox is checked, the property will be styled like the corresponding property defined in ";
    
    public final static String DEFAULT_CSS_PATH = "resources/css/sequentStyleDefault.css";
    public final static String DEFAULT_XML_PATH = "resources/xml/cssList.xml";
    public final static String KEY_WINDOW_ICON = "file:resources/images/key-color-icon-square.png";
    public final static String FILTER_MOUSE_ICON = "file:resources/images/mouse_icon.png";
    public final static String PROJECT_URL = "http://www.key-project.org/";

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