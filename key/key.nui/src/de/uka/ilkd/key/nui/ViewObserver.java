package de.uka.ilkd.key.nui;

import java.util.Observable;
import java.util.Observer;

import de.uka.ilkd.key.model.ViewInformation;
import de.uka.ilkd.key.nui.view.RootLayoutController;

public class ViewObserver implements Observer {
    private RootLayoutController container;

    public ViewObserver(RootLayoutController container) {
        this.container = container;
    }

    @Override
    public void update(Observable observable, Object arg1) {
        if (!(observable instanceof ViewInformation))
            return;
        boolean activeUpdated = (boolean) arg1;

        ViewInformation info = (ViewInformation) observable;

        if (activeUpdated) {
            if (info.getIsActive())
                container.showView(info);
            else
                container.hideView(info.getTitle());
            container.checkViewMenuItem(info.getTitle(), info.getIsActive());
        }
        else
            container.moveView(info.getTitle(), info.getCurrentPosition());
    }
}
