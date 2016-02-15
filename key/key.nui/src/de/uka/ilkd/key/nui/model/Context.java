package de.uka.ilkd.key.nui.model;

import java.nio.file.DirectoryStream.Filter;
import java.util.List;
import java.util.function.Consumer;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.nui.MediatorUserInterface;
import de.uka.ilkd.key.nui.StatusManager;
import de.uka.ilkd.key.nui.filter.Criteria;
import de.uka.ilkd.key.nui.filter.FilterChangedEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.nui.filter.SelectModeEventArgs;
import de.uka.ilkd.key.nui.util.CsEvent;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.NUIConstants;

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

    private CsEvent<FilterChangedEventArgs> filterChangedEvent = new CsEvent<>();

    public CsEvent<FilterChangedEventArgs> getFilterChangedEvent() {
        return filterChangedEvent;
    }

    private Criteria<Pair<Integer,String>> currentFilterCriteria = null;
    private FilterLayout currentFilterLayout;

    public void setCurrentFilterCriteria(Criteria<Pair<Integer,String>> criteria, FilterLayout layout) {
        currentFilterCriteria = criteria;
        currentFilterLayout = layout;
        filterChangedEvent.fire(new FilterChangedEventArgs(layout,criteria));
    }

    public Criteria<Pair<Integer,String>> getCurrentPrintFilter() {
        return currentFilterCriteria;
    }
    
    public FilterLayout getCurrentFilterLayout(){
        return currentFilterLayout;
    }

    private CsEvent<String> sequentHtmlChangedEvent = new CsEvent<>();

    public CsEvent<String> getSequentHtmlChangedEvent() {
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
    
    public CssFileHandler getCssFileHandler(){
        if (cssFileHandler == null) try {
            cssFileHandler = new CssFileHandler(NUIConstants.DEFAULT_STYLE_CSS);  
        }
        catch (Exception e) {
            System.err.println("Could not load CSS. No beauty for you!");
        }
        return cssFileHandler;
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
