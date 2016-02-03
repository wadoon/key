package de.uka.ilkd.key.nui.viewmediation;

import de.uka.ilkd.key.nui.view.DebugViewController;

/**
 * used for decoupling
 * just wrap all methods/functions that should be callable from other views
 * @author Benedikt Gross
 *
 */
//TOCHECK Method 1
public class DebugViewProxy extends DereferedViewProxy {

    private DebugViewController controller;
    public DebugViewProxy(DebugViewController controller){
        this.controller = controller;
    }
    
    public void print(String str) {
        controller.print(str);
    }
}
