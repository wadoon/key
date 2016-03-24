package de.uka.ilkd.key.nui;

import java.util.Observable;
import java.util.Observer;

import de.uka.ilkd.key.nui.view.RootLayoutController;

/**
 * TODO add documentation
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class ViewObserver implements Observer {
    private RootLayoutController container;

    /**
     * Use the constructor to set the {@link RootLayoutController}.
     * 
     * @param container
     *            RootLayoutController
     */
    public ViewObserver(RootLayoutController container) {
        this.container = container;
    }

    @Override
    public void update(Observable observable, Object arg1) {
        if (!(observable instanceof ViewInformation)) {
            return;
        }
        boolean activeUpdated = (boolean) arg1;

        ViewInformation info = (ViewInformation) observable;

        if (activeUpdated) {
            if (info.getIsActive())
                container.showView(info);
            else
                container.hideView(info);
            container.checkViewMenuItem(info.getTitle(), info.getIsActive());
        }
        else
            container.moveView(info, info.getCurrentPosition());
    }
}
