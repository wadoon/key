package de.uka.ilkd.key.nui.util;

/**
 * Collection of constants used throughout the application.
 * 
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Nils Muzzulini
 * @version 1.0
 */
public final class NUIConstants {
    /**
     * CSS Style constants
     */
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

    /**
     * CSS Styler constants
     */
    public final static String CSSSTYLER_COLOR_TT_TEXT = "Pick a Color";
    public final static String CSSSTYLER_WEIGHT_TT_TEXT = "Choose the Boldness";
    public final static String CSSSTYLER_STYLE_TT_TEXT = "Turn Italics on/off";
    public final static String CSSSTYLER_SIZE_TT_TEXT = "Choose the Font Size";
    public final static String CSSSTYLER_FONT_TT_TEXT = "Choose a Font.\n"
            + "The SequentView might not be able to render every Font.\n" + "This is due to WebBrowser Compability.";
    public final static String CSSSTYLER_OTHER_TT_TEMPLATE = "Edit ";
    public final static String CSSSTYLER_INHERITED_TT_TEMPLATE = "If this checkbox is checked, the property will be styled like the corresponding property defined in ";

    public final static String PREFERENCES_CSSPATH_KEY = "cssPath";

    /**
     * Default CSS and XML paths
     */
    public final static String DEFAULT_CSS_PATH = "resources/css/sequentStyleDefault.css";
    public final static String DEFAULT_XML_PATH = "resources/xml/cssList.xml";

    /**
     * Icons
     */
    public final static String KEY_APPLICATION_WINDOW_ICON_PATH = "file:resources/images/key-color-icon-square.png";
    public final static String FILTER_MOUSE_ICON_PATH = "file:resources/images/mouse_icon.png";
    public final static String CLOSED_PROOF_ICON_PATH = "file:resources/images/keyproved.gif";
    public final static String OPEN_PROOF_ICON_PATH = "file:resources/images/ekey-mono.gif";
    public final static String CLOSED_PROOF_BUT_OPEN_LEMMAS_LEFT_ICON_PATH = "file:resources/images/ekey-brackets.gif";

    /**
     * Project URL
     */
    public final static String PROJECT_URL = "http://www.key-project.org/";
    
    /**
     * Tips of the Day
     */
    public final static String TIPS_OF_THE_DAY_PATH = "resources/tipsOfTheDay";
}