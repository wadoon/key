package de.uka.ilkd.key.nui;

import java.util.prefs.Preferences;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.nui.event.HandlerEvent;
import de.uka.ilkd.key.nui.filter.FilterChangedEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.SelectModeEventArgs;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.nui.util.XmlReader;
import de.uka.ilkd.key.nui.view.menu.TacletMenuItem;
import javafx.collections.ObservableList;

public class Context {

    private KeYMediator mediator = null;
    private MainApp mainApp;
    private MediatorUserInterface userInterface;

    public MediatorUserInterface getUserInterface() {
        return userInterface;
    }

    /**
     * Lazy loaded KeyMediator
     * 
     * @return the current or a new KeYMediator
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
     * Lazy loaded StatusManager
     * 
     * @return
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

    public void setCurrentFilter(PrintFilter filter) {
        currentPrintFilter = filter;
        filterChangedEvent.fire(new FilterChangedEventArgs(currentPrintFilter));
    }

    public PrintFilter getCurrentPrintFilter() {
        return currentPrintFilter;
    }

    private HandlerEvent<String> sequentHtmlChangedEvent = new HandlerEvent<>();

    public HandlerEvent<String> getSequentHtmlChangedEvent() {
        return sequentHtmlChangedEvent;
    }

    private String sequentHtml;

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

    public CssFileHandler getCssFileHandler() {
        if (cssFileHandler == null)
            try {
                Preferences prefs = Preferences
                        .userNodeForPackage(this.getClass());
                String path = prefs.get(NUIConstants.PREFERENCES_CSSPATH_KEY,
                        NUIConstants.DEFAULT_CSS_PATH);
                cssFileHandler = new CssFileHandler(path);
            }
            catch (Exception e) {
                System.err.println("Could not load CSS. No beauty for you!");
            }
        return cssFileHandler;
    }

    private XmlReader xmlReader;

    public XmlReader getXmlReader() {
        if (xmlReader == null || cssFileHandler == null) {
            cssFileHandler = getCssFileHandler();

            xmlReader = new XmlReader(NUIConstants.DEFAULT_XML_PATH,
                    cssFileHandler.getParsedRules());
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

    public Context(MainApp mainApp) {
        this.mainApp = mainApp;
    }

    private TacletInstantiationModel[] models;

    public void setCurrentModels(TacletInstantiationModel[] models) {
        if (models == null) {
            return;
        }
        this.models = (TacletInstantiationModel[]) models.clone();
    }

    public TacletInstantiationModel[] getCurrentModels() {
        if (models == null) {
            return new TacletInstantiationModel[0];
        }
        return (TacletInstantiationModel[]) models.clone();
    }

    private ObservableList<TacletMenuItem> hiddenTacletMenuItems;

    public void setCurrentHiddenTacletMenuItems(
            ObservableList<TacletMenuItem> hiddenItems) {
        this.hiddenTacletMenuItems = hiddenItems;
    }

    public ObservableList<TacletMenuItem> getCurrentHiddenTacletMenuItems() {
        return hiddenTacletMenuItems;
    }
}
