package de.uka.ilkd.key.nui.model;

import java.nio.file.DirectoryStream.Filter;
import java.util.List;
import java.util.function.Consumer;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.nui.MediatorUserInterface;
import de.uka.ilkd.key.nui.StatusManager;
import de.uka.ilkd.key.nui.filter.Criteria;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.SelectModeEventArgs;
import de.uka.ilkd.key.nui.util.CsEvent;
import de.uka.ilkd.key.util.Pair;

public class Context {

    private KeYMediator mediator = null;

    /**
     * Lazy loaded KeyMediator
     * 
     * @return the current or a new KeYMediator
     */
    public KeYMediator getKeYMediator() {
        if (mediator == null) {
            MediatorUserInterface userInterface = new MediatorUserInterface(
                    statusManager);
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

    private CsEvent<PrintFilter> filterChangedEvent = new CsEvent<>();

    public CsEvent<PrintFilter> getFilterChangedEvent() {
        return filterChangedEvent;
    }

    private PrintFilter currentPrintFilter = null;

    public void setCurrentPrintFilter(PrintFilter filter) {
        currentPrintFilter = filter;
        filterChangedEvent.fire(filter);
    }

    public PrintFilter getCurrentPrintFilter() {
        return currentPrintFilter;
    }

    private CsEvent<String> sequentHtmlChangedEvent = new CsEvent<>();

    public CsEvent<String> getSequentHtmlChangedEvent() {
        return sequentHtmlChangedEvent;
    }

    private String sequentHtml;

    public void setSequentHtml(String value) {
        if (value == sequentHtml)
            return;
        sequentHtml = value;
        sequentHtmlChangedEvent.fire(value);
    }

    public String getSequentHtml() {
        return sequentHtml;
    }

    private CsEvent<SelectModeEventArgs> selectModeActivatedEvent = new CsEvent<>();

    public CsEvent<SelectModeEventArgs> getSelectModeActivateEvent() {
        return selectModeActivatedEvent;
    }

    public void activateSelectMode(FilterSelection filterSelection) {
        selectModeActivatedEvent.fire(new SelectModeEventArgs(filterSelection));
    }

    public Context() {
    }
}
