package de.uka.ilkd.key.nui.util;

import org.w3c.dom.css.CSSRule;

/**
 * Collection of constants used throughout the application.
 * 
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Nils Muzzulini
 * @version 1.0
 */
public final class NUIConstants {
    /*
     * CSS Style constants
     */

    /**
     * The beginning Constant for opening span tags used for HTML Styling. Do
     * not forget to use OPEN_TAG_END
     */
    public final static String OPEN_TAG_BEGIN = "<span class=\"";
    /**
     * The ending Constant for opening span tags used for HTML Styling. Do not
     * forget to use OPEN_TAG_BEGIN
     */
    public final static String OPEN_TAG_END = "\">";
    /**
     * Constant for closing span tags
     */
    public final static String CLOSING_TAG = "</span>";

    /*
     * CSS Class constants for not Syntax Highlighting
     */

    /**
     * Constant for general Text styling and whitespace formatting
     */
    public final static String MASTER_TAG = "pre";
    /**
     * Constant for MouseoverHighlighting
     */
    public final static String MOUSE_TAG = "mouseover";
    /**
     * Constant for SearchHighlighting
     */
    public final static String HIGHLIGHTED_TAG = "highlighted";
    /**
     * Constant for FilterSelection Highlighting
     */
    public final static String FILTER_SELECTION_TAG = "filterSelection";
    /**
     * Constant for minimizing Filtering
     */
    public final static String FILTER_MINIMIZED_TAG = "minimized";
    /**
     * Constant for collapsing Filtering
     */
    public final static String FILTER_COLLAPSED_TAG = "collapsed";
    /**
     * Constant for Rule Application Highlighting
     */
    public final static String RULE_APP_TAG = "ruleApp";
    /**
     * Constant for Instantiation Highlighting in RuleApplication Context
     */
    public final static String IF_INST_TAG = "ifInst";
    /**
     * Constant for Formula Highlighting in RuleApplication Context
     */
    public final static String IF_FORMULA_TAG = "ifFormula";

    /*
     * CSS Styler Tooltips constants
     */

    /**
     * Tooltip Text for ColorPicker
     */
    public final static String CSSSTYLER_COLOR_TT_TEXT = "Pick a Color";
    /**
     * Tooltip Text for FontWeight Dropdown menu
     */
    public final static String CSSSTYLER_WEIGHT_TT_TEXT = "Choose the Boldness";
    /**
     * Tooltip Text for Italic Setting Dropdown menu
     */
    public final static String CSSSTYLER_STYLE_TT_TEXT = "Turn Italics on/off";
    /**
     * Tooltip Text for Font Size Control
     */
    public final static String CSSSTYLER_SIZE_TT_TEXT = "Choose the Font Size";
    /**
     * Tooltip Text for Font Dropdown menu
     */
    public final static String CSSSTYLER_FONT_TT_TEXT = "Choose a Font.\n"
            + "The SequentView might not be able to render every Font.\n"
            + "This is due to WebBrowser Compability.";
    /**
     * Tooltip Template for unaccounted CSS properties. Append the propertyName
     * for a comprehensive tooltip
     */
    public final static String CSSSTYLER_OTHER_TT_TEMPLATE = "Edit ";
    /**
     * Tooltip Template for inherited CSS properties. Append the Description of
     * the {@link CSSRule} to be inherited from for a comprehensive tooltip
     */
    public final static String CSSSTYLER_INHERITED_TT_TEMPLATE = "If this checkbox is checked, the property will be styled like the corresponding property defined in ";

    public final static String PREFERENCES_CSSPATH_KEY = "cssPath";

    /*
     * Default CSS and XML paths
     */

    /**
     * The path to the default CSS for the sequent view highlighting.
     */
    public final static String DEFAULT_CSS_PATH = "resources/css/sequentStyleDefault.css";
    /**
     * The path to the default XML containing the CSS selectors.
     */
    public final static String DEFAULT_XML_PATH = "resources/xml/cssList.xml";

    /*
     * Icons
     */

    /**
     * The path to the KeY logo to use as window icon.
     */
    public final static String KEY_APPLICATION_WINDOW_ICON_PATH = "file:resources/images/key-color-icon-square.png";
    /**
     * The path to the icon for the selection filter button.
     */
    public final static String FILTER_MOUSE_ICON_PATH = "file:resources/images/mouse_icon.png";
    /**
     * The path to the closed proof icon.
     */
    public final static String CLOSED_PROOF_ICON_PATH = "file:resources/images/keyproved.gif";
    /**
     * The path to the open proof icon.
     */
    public final static String OPEN_PROOF_ICON_PATH = "file:resources/images/ekey-mono.gif";
    /**
     * The path to the proof icon in brackets.
     */
    public final static String CLOSED_PROOF_BUT_OPEN_LEMMAS_LEFT_ICON_PATH = "file:resources/images/ekey-brackets.gif";

    /**
     * Project URL
     */
    public final static String PROJECT_URL = "http://www.key-project.org/";

    /**
     * Path to the 'Tips of the Day'
     */
    public final static String TIPS_OF_THE_DAY_PATH = "resources/tipsOfTheDay";

    /**
     * The maximum number of recent files displayed in the recent file menu.
     */
    public static final int MAX_RECENT_FILES = 8;

    /**
     * The delay in milliseconds (1000 milliseconds = 1 second) for the sequent
     * search to start searching after the last key pressed.
     */
    public final static long SEQUENT_SEARCH_DELAY_IN_MILLISECONDS = 0;
}