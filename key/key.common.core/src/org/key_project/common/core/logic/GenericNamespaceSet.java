package org.key_project.common.core.logic;

/**
 * 
 * TODO: Document.
 *
 */
public interface GenericNamespaceSet {

    /**
     * Returns the {@link Namespace} with the given name (e.g., "functions") or
     * null if there exists no such {@link Namespace}. For any name returned by
     * {@link #getNamespaceNames()}, the result will be non-null.
     *
     * @param name
     *            Name of the {@link Namespace} to return. The name is supposed
     *            to be in lower-case letters.
     * @return the {@link Namespace} of the given name.
     */
    Namespace getNamespace(String name);

    /**
     * @return the names of the available {@link Namespace}s. For any of those,
     *         {@link #getNamespace(String)} will return a concrete
     *         {@link Namespace}.
     */
    String[] getNamespaceNames();

    /**
     * Looks up if the given name is found in one of the namespaces and returns
     * the named object or null if no object with the same name has been found.
     *
     * @param name
     *            The name of the object to look up.
     * @return The named object looked for or null if there is no such object.
     */
    Named lookup(Name name);

    /**
     * TODO: Document.
     *
     * @return The functions set.
     * @deprecated Is here for backwards compatibility; you should use
     *             {@link #getNamespace(String)} instead to be compatible with
     *             other logics than JavaDL.
     */
    Namespace functions();

    /**
     * TODO: Document.
     *
     * @return The sorts set.
     * @deprecated Is here for backwards compatibility; you should use
     *             {@link #getNamespace(String)} instead to be compatible with
     *             other logics than JavaDL.
     */
    Namespace sorts();
}
