package de.uka.ilkd.key.nui;

import java.io.File;
import java.lang.reflect.Array;
import java.util.prefs.Preferences;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.TacletMenu;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.event.HandlerEvent;
import de.uka.ilkd.key.nui.filter.FilterChangedEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.SelectModeEventArgs;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.nui.util.XmlReader;
import de.uka.ilkd.key.nui.view.SequentViewController;
import de.uka.ilkd.key.nui.view.menu.TacletMenuItem;
import javafx.collections.ObservableList;

/**
 * A central collection of all major components to be used throughout the
 * application including the {@link KeYMediator}, {@link MediatorUserInterface},
 * {@link StatusManager}, {@link PrintFilter}, {@link CssFileHandler},
 * {@link XmlReader} and {@link TacletInstantiationModel
 * TacletInstantiationModels} as well as some {@link HandlerEvent custom event
 * handlers}.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class Context {

    private KeYMediator mediator = null;
    private MainApp mainApp;
    private MediatorUserInterface userInterface;

    /**
     * @return The current {@link MediatorUserInterface}.
     */
    public MediatorUserInterface getUserInterface() {
        return userInterface;
    }

    /**
     * Lazy loaded {@link KeYMediator}.
     * 
     * @return The current or a new {@link KeYMediator}.
     */
    public KeYMediator getKeYMediator() {
        if (mediator == null) {
            userInterface = new MediatorUserInterface(statusManager, mainApp);
            mediator = new KeYMediator(userInterface);
            userInterface.setMediator(mediator);
        }
        return mediator;
    }

    private StatusManager statusManager = null;

    /**
     * Lazy loaded {@link StatusManager}.
     * 
     * @return The current or a new {@link StatusManager}.
     */
    public StatusManager getStatusManager() {
        if (statusManager == null)
            statusManager = new StatusManager();
        return statusManager;
    }

    private HandlerEvent<FilterChangedEventArgs> filterChangedEvent = new HandlerEvent<>();

    public HandlerEvent<FilterChangedEventArgs> getFilterChangedEvent() {
        return filterChangedEvent;
    }

    private PrintFilter currentPrintFilter;

    /**
     * @param filter
     *            The {@link PrintFilter} to be set.
     */
    public void setCurrentFilter(PrintFilter filter) {
        currentPrintFilter = filter;
        filterChangedEvent.fire(new FilterChangedEventArgs(currentPrintFilter));
    }

    /**
     * @return The current {@link PrintFilter}.
     */
    public PrintFilter getCurrentPrintFilter() {
        return currentPrintFilter;
    }

    private HandlerEvent<String> sequentHtmlChangedEvent = new HandlerEvent<>();

    public HandlerEvent<String> getSequentHtmlChangedEvent() {
        return sequentHtmlChangedEvent;
    }

    private String sequentHtml = null;

    /**
     * Sets a new {@link String} value to be set as new {@link Sequent} html and
     * fires a "sequent changed event".
     * 
     * @param value
     *            The new value to be put in the {@link SequentViewController}.
     */
    public void setSequentHtml(String value) {
        if (value.equals(sequentHtml))
            return;
        sequentHtml = value;
        sequentHtmlChangedEvent.fire(value);
    }

    public String getSequentHtml() {
        return sequentHtml;
    }

    private CssFileHandler cssFileHandler;

    /**
     * Lazy loaded {@link CssFileHandler}.
     * 
     * @return The current or a new {@link CssFileHandler}.
     */
    public CssFileHandler getCssFileHandler() {
        if (cssFileHandler == null) {
            try {
                Preferences prefs = Preferences.userNodeForPackage(this.getClass());
                String path = prefs.get(NUIConstants.PREFERENCES_CSSPATH_KEY, NUIConstants.DEFAULT_CSS_PATH);
                File testFile = new File(path);

                // Failsafe if File is Missing
                if (!testFile.exists() || testFile.isDirectory()) {
                    prefs.put(NUIConstants.PREFERENCES_CSSPATH_KEY, NUIConstants.DEFAULT_CSS_PATH);
                    path = NUIConstants.DEFAULT_CSS_PATH;
                }

                cssFileHandler = new CssFileHandler(path);
            }
            catch (Exception e) {
                System.err.println("Could not load CSS. No beauty for you!");
            }
        }
        return cssFileHandler;
    }

    private XmlReader xmlReader;

    /**
     * Lazy loaded {@link XmlReader}.
     * 
     * @return The current or a new {@link XmlReader}.
     */
    public XmlReader getXmlReader() {
        if (xmlReader == null || cssFileHandler == null) {
            cssFileHandler = getCssFileHandler();

            xmlReader = new XmlReader(NUIConstants.DEFAULT_XML_PATH, cssFileHandler.getParsedRules());
        }
        return xmlReader;
    }

    private HandlerEvent<SelectModeEventArgs> selectModeActivatedEvent = new HandlerEvent<>();

    public HandlerEvent<SelectModeEventArgs> getSelectModeActivateEvent() {
        return selectModeActivatedEvent;
    }

    public void activateSelectMode(FilterSelection filterSelection) {
        selectModeActivatedEvent.fire(new SelectModeEventArgs(filterSelection));
    }

    /**
     * Constructor sets the associated {@link MainApp}.
     * 
     * @param mainApp
     *            {@link MainApp}.
     */
    public Context(MainApp mainApp) {
        this.mainApp = mainApp;
    }

    private TacletInstantiationModel[] models;

    /**
     * Replaces the {@link TacletInstantiationModel}s with new ones.
     * 
     * @param models
     *            {@link Array} of {@link TacletInstantiationModel
     *            TacletInstantiationModels}.
     */
    public void setCurrentModels(TacletInstantiationModel[] models) {
        if (models == null) {
            return;
        }
        this.models = (TacletInstantiationModel[]) models.clone();
    }

    /**
     * @return An {@link Array} of current {@link TacletInstantiationModel
     *         TacletInstantiationModel}.
     */
    public TacletInstantiationModel[] getCurrentModels() {
        if (models == null) {
            return new TacletInstantiationModel[0];
        }
        return (TacletInstantiationModel[]) models.clone();
    }

    private ObservableList<TacletMenuItem> hiddenTacletMenuItems;

    /**
     * Sets a collection of {@link TacletMenuItem}s to be hidden in the
     * {@link TacletMenu}.
     * 
     * @param hiddenItems
     *            An {@link ObservableList} of {@link TacletMenuItem}.
     */
    public void setCurrentHiddenTacletMenuItems(ObservableList<TacletMenuItem> hiddenItems) {
        this.hiddenTacletMenuItems = hiddenItems;
    }

    /**
     * @return An {@link ObservableList} of hidden {@link TacletMenuItem
     *         TacletMenuItems},
     */
    public ObservableList<TacletMenuItem> getCurrentHiddenTacletMenuItems() {
        return hiddenTacletMenuItems;
    }
}
