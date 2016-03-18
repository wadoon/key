package de.uka.ilkd.key.nui.prooftree;

import java.io.File;
import java.io.FileNotFoundException;
import java.lang.annotation.Annotation;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Observable;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.prooftree.filter.FilterAnnotation;
import de.uka.ilkd.key.nui.prooftree.filter.FilterCombineAND;
import de.uka.ilkd.key.nui.prooftree.filter.FilterShowAll;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;

/**
 * Handles the filtering of the proof tree.
 * 
 * @author Matthias Schultheis
 * @author Florian Breitfelder
 *
 */
public class FilteringHandler {

    /**
     * A map storing filters with their respective activation flag.
     */
    final private Map<ProofTreeFilter, Boolean> filtersMap = Collections
            .synchronizedMap(new LinkedHashMap<>());

    /**
     * The data model.
     */
    final private DataModel dataModel;

    /**
     * Constructor.
     * 
     * @param model
     *            The DataModel.
     * @throws FileNotFoundException
     */
    public FilteringHandler(final DataModel model) {
        this.dataModel = model;

        // Load filters and store all loaded filters into the filtersMap
        final List<ProofTreeFilter> filters = searchFilterClasses();
        filters.forEach((filter) -> filtersMap.put(filter, false));

        // Reinitialize filters if the data model changed
        model.addObserver((final Observable obs, final Object arg) -> {
            reinit();
        });
    }

    /**
     * Resets all active filters.
     */
    public final void reinit() {
        filtersMap.forEach((filter, active) -> {
            if (active) {
                filtersMap.put(filter, false);
            }
        });
    }

    /**
     * Searches for applicable filters in the package
     * de.uka.ilkd.key.nui.prooftree.filter.
     * 
     * @return A list of filters
     */
    private List<ProofTreeFilter> searchFilterClasses() {
        final List<ProofTreeFilter> filters = new LinkedList<>();

        // Path were filter class's are stored
        final String PATH = "filter/";
        // Prefix for binary class names
        final String BINARY_NAME_PREFIX = "de.uka.ilkd.key.nui.prooftree.filter.";

        // Look for all class files in PATH and store their URLs
        File[] files = new File(getClass().getResource(PATH).getPath())
                .listFiles();
        ArrayList<URL> listOfURLs = new ArrayList<>();

        try {
            for (File file : files) {
                if (file.isFile() && file.getName().matches(".*[.class]")) {
                    try {
                        URL urlClassFile = file.toURI().toURL();
                        listOfURLs.add(urlClassFile);
                    }
                    catch (MalformedURLException e) {
                        e.printStackTrace();
                    }
                }
            }
        }
        catch (Exception e) {
            System.out.println((getClass().getName() + ": " + "Path " + PATH
                    + " not found."));
        }

        // Convert listOfURLs to an array of URLs. This array is needed for the
        // classLoader
        URL[] urls = new URL[listOfURLs.size()];
        urls = listOfURLs.toArray(urls);

        ClassLoader classLoader = null;
        try {
            // initialize classLoader
            classLoader = new URLClassLoader(urls);
            String binaryClassName = null;

            for (File file : files) {
                // build binaryClassName to load class with classLoader
                binaryClassName = BINARY_NAME_PREFIX + file.getName()
                        .substring(0, file.getName().lastIndexOf("."));

                // Load possible filter class
                Class<?> c = classLoader.loadClass(binaryClassName);
                // Load annotations of the class
                Annotation[] annotations = c
                        .getAnnotationsByType(FilterAnnotation.class);

                // check if isFilter is true
                for (Annotation annotation : annotations) {
                    /*
                     * If the annotation isFilter is true, the current class is
                     * a valid filter class therefore create a new instance of
                     * it and add it to filters.
                     */
                    if (((FilterAnnotation) annotation).isFilter()) {
                        filters.add((ProofTreeFilter) c.newInstance());
                    }
                }
            }
        }
        catch (ClassNotFoundException | InstantiationException
                | IllegalAccessException e) {
            e.printStackTrace();
        }

        return filters;
    }

    /**
     * Returns a list of the currently active filters.
     * 
     * @return A list of the currently active filters.
     */
    private List<ProofTreeFilter> getActiveFilters() {

        final List<ProofTreeFilter> filters = new LinkedList<>();

        filtersMap.forEach((filter, active) -> {
            if (active) {
                filters.add(filter);
            }
        });

        return filters;
    }

    /**
     * Applies the filters that are currently set to active.
     */
    private void applyFilters() {
        final List<ProofTreeFilter> activeFilters = getActiveFilters();

        // reduces all active filers to one
        final ProofTreeFilter redFilter = activeFilters.stream()
                .reduce(new FilterShowAll(), (f1, f2) -> {
                    return new FilterCombineAND(f1, f2);
                });

        final ProofTreeItem root;
        if (dataModel.getLoadedTreeViewState() != null) {
            root = dataModel.getLoadedTreeViewState().getTreeItem();
            root.filter(redFilter);
        }
    }

    /**
     * Returns the list of loaded filters.
     * 
     * @return the {@link #filtersMap}.
     */
    public Map<ProofTreeFilter, Boolean> getFiltersMap() {
        return filtersMap;
    }

    /**
     * Returns the activation status for a filter.
     * 
     * @param filter
     *            The filter to check
     * @return true iff the filter is activated
     */
    public boolean getFilterStatus(final ProofTreeFilter filter) {
        return filtersMap.get(filter);
    }

    /**
     * Toggles the activation status for a filter.
     * 
     * @param filter
     *            The filter to change the status of.
     */
    public void toggleFilteringStatus(final ProofTreeFilter filter) {
        final boolean newState = !filtersMap.get(filter);
        filtersMap.put(filter, newState);

        applyFilters();
    }

}
