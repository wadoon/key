package de.uka.ilkd.key.nui.viewmediation;

/**
 * Interface that all views must implement to be called view proxy
 * @author Benedikt Gross
 *
 */
public interface ViewProxyProvider {
    public DereferedViewProxy getProxy();
}
