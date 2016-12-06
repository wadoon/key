package de.tud.cs.se.ds.psec.util;

import java.net.URL;
import java.util.Optional;

/**
 * Access to bundled resources.
 *
 * @author Dominic Scheurer
 */
public class ResourceManager {
    private static final ResourceManager INSTANCE = new ResourceManager();

    //@formatter:off
    private ResourceManager() {}
    //@formatter:on

    public static ResourceManager instance() {
        return INSTANCE;
    }

    /**
     * Loads a resource and returns its URL.
     * 
     * @param cl
     *            The Class used to determine the resource.
     * @param resourcename
     *            The String that contains the name of the resource.
     * @return The URL of the resource.
     */
    public Optional<URL> getResourceFile(Class<?> cl, String resourcename) {
        URL resourceURL = cl.getResource(resourcename);
        if (resourceURL == null && cl.getSuperclass() != null) {
            return getResourceFile(cl.getSuperclass(), resourcename);
        }
        else if (resourceURL == null && cl.getSuperclass() == null) {
            return Optional.empty();
        }
        return Optional.of(resourceURL);
    }

    /**
     * Loads a resource and returns its URL.
     * 
     * @param o
     *            The Object used to determine the resource.
     * @param resourcename
     *            The String that contains the name of the resource.
     * @return The URL of the resource.
     */
    public Optional<URL> getResourceFile(Object o, String resourcename) {
        return getResourceFile(o.getClass(), resourcename);
    }

}
