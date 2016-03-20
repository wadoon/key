package de.uka.ilkd.key.nui.view.menu;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Properties;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.Debug;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

public class RecentFileMenu {
    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;

    /** this is the maximal number of recent files. */
    private int maxNumberOfEntries;

    private EventHandler<ActionEvent> actionHandler;

    private Menu menu;

    /**
     * list of recent files
     */
    private HashMap<MenuItem, RecentFileEntry> recentFiles;

    private RecentFileEntry mostRecentFile;

    /**
     * Create a new RecentFiles list.
     * 
     * @param listener
     *            the ActionListener that will be notified of the user clicked
     *            on a recent file menu entry. The selected filename can be
     *            determined with the ActionEvent's getSource() method, cast the
     *            Object into a JMenuItem and call the getLabel() method.
     * @param maxNumberOfEntries
     *            the maximal number of items/entries in the recent file menu.
     * @param p
     *            a Properties object containing information about the recent
     *            files to be displayed initially. Or <code>null</code> to use
     *            no initial information.
     */
    public RecentFileMenu(final KeYMediator mediator) {
        this.menu = new Menu("Recent Files");
        this.maxNumberOfEntries = MAX_RECENT_FILES;
        this.recentFiles = new LinkedHashMap<MenuItem, RecentFileEntry>();

        actionHandler = new EventHandler<ActionEvent>() {

            @Override
            public void handle(ActionEvent event) {
                mediator.getUI().loadProblem(new File(getAbsolutePath((MenuItem) event.getSource())));
            }

        };

        menu.setDisable(menu.getItems().size() != 0);

        load(PathConfig.getRecentFileStorage());
    }

    /**
     */
    private void removeFromModelAndView(MenuItem item, int index) {
        recentFiles.remove(item);
        menu.getItems().remove(index);
    }

    /**
     * add file name to the menu
     */
    private void addToModelAndView(final String name) {
        // do not add quick save location to recent files
        if (de.uka.ilkd.key.gui.actions.QuickSaveAction.QUICK_SAVE_PATH.endsWith(name))
            return;

        final RecentFileEntry entry = new RecentFileEntry(name);
        if (new File(entry.getAbsolutePath()).exists()) {
            MenuItem item = new MenuItem(entry.getFileName());
            // item.setToolTipText(entry.getAbsolutePath());
            recentFiles.put(item, entry);
            menu.getItems().add(0, item);
            mostRecentFile = entry;
            item.setOnAction(actionHandler);
        }
    }

    /**
     *
     */
    public String getAbsolutePath(MenuItem item) {
        return recentFiles.get(item).getAbsolutePath();
    }

    /**
     * call this method to add a new file to the beginning of the RecentFiles
     * list. If the name is already part of the list, it will be moved to the
     * first position. No more than a specified maximum number of names will be
     * allowed in the list, and additional names will be removed at the end.
     * (set the maximum number with the {@link #setMaxNumberOfEntries(int i)}
     * method).
     * 
     * @param name
     *            the name of the file.
     */
    public void addRecentFile(final String name) {
        // Add the name to the recentFileList:
        // check whether this name is already there
        Debug.out("recentfilemenu: add file: ", name);
        Debug.out("recentfilemenu: at menu count:", menu.getItems().size());
        int index = -1;
        MenuItem item = null;
        for (int i = 0; i < menu.getItems().size(); i++) {
            if (menu.getItems().get(i) == null) {
                continue;
            }
            Debug.out("", i);
            Debug.out("item is ", menu.getItems().get(i));
            Debug.out("name is ", menu.getItems().get(i).getText());
            if (recentFiles.get(menu.getItems().get(i)).getAbsolutePath().equals(name)) {
                // this name has to be put at the first position
                item = menu.getItems().get(i);
                index = i;
                break;
            }
        }

        if (index != -1) {
            // move the name to the first position
            removeFromModelAndView(item, index);
        }
        // if appropriate, remove the last entry.
        if (menu.getItems().size() == maxNumberOfEntries) {
            removeFromModelAndView(menu.getItems().get(menu.getItems().size() - 1), menu.getItems().size() - 1);
        }
        addToModelAndView(name);
        // menu.setEnabled(menu.getItems().size() != 0);
    }

    /**
     * specify the maximal number of recent files in the list. The default is
     * MAX_RECENT_FILES
     */
    public void setMaxNumberOfEntries(int max) {
        if (maxNumberOfEntries > max && menu.getItems().size() > max) {
            for (int i = menu.getItems().size() - 1; i > max; i--) {
                menu.getItems().remove(i);
            }

        }
        this.maxNumberOfEntries = max;
    }

    /**
     * the menu where the recent files are kept. If the user didn't specify one
     * in the constructor, a new JMenu is created. It can be accessed via this
     * method.
     */
    public Menu getMenu() {
        return menu;
    }

    /**
     * read the recent file names from the properties object. the property names
     * are expected to be "RecentFile0" "RecentFile1" ...
     */
    public void load(Properties p) {
        int i = maxNumberOfEntries;
        String s;
        do {
            s = p.getProperty("RecentFile" + i);
            if (s != null)
                addRecentFile(s);
            i--;
        }
        while (i >= 0);
    }

    /**
     * Put the names of the recent Files into the properties object. The
     * property names are "RecentFile0" "RecentFile1" ... The values are fully
     * qualified path names.
     */
    public void store(Properties p) {
        // if there's nothing to store:
        for (int i = 0; i < menu.getItems().size(); i++) {
            p.setProperty("RecentFile" + i, getAbsolutePath(menu.getItems().get(i)));
        }
    }

    /** read the recent files from the given properties file */
    public final void load(String filename) {
        FileInputStream propStream = null;
        try {
            propStream = new FileInputStream(filename);
            Properties p = new Properties();
            p.load(propStream);
            Enumeration<?> e = p.propertyNames();
            while (e.hasMoreElements()) {
                String s = (String) e.nextElement();
                if (s.indexOf("RecentFile") != -1)
                    addRecentFile(p.getProperty(s));
            }
        }
        catch (FileNotFoundException ex) {
            Debug.out("Could not read RecentFileList. Did not find file ", filename);
        }
        catch (IOException ioe) {
            Debug.out("Could not read RecentFileList. Some IO Error occured ", ioe);
        }
        finally {
            try {
                if (propStream != null) {
                    propStream.close();
                }
            }
            catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    public RecentFileEntry getMostRecent() {
        return mostRecentFile;
    }

    /**
     * write the recent file names to the given properties file. the file will
     * be read (if it exists) and then re-written so no information will be
     * lost.
     */
    public void store(String filename) {
        File localRecentFiles = new File(filename);
        FileInputStream fin = null;
        FileOutputStream fout = null;
        Properties p = new Properties();
        try {
            // creates a new file if it does not exist yet
            localRecentFiles.createNewFile();
            fin = new FileInputStream(localRecentFiles);
            fout = new FileOutputStream(localRecentFiles);
            p.load(fin);
            store(p);
            p.store(fout, "recent files");
        }
        catch (IOException ex) {
            System.err.println("Cound not write recentFileList due to " + ex.toString() + "::" + localRecentFiles);
        }
        finally {
            try {
                if (fin != null)
                    fin.close();
            }
            catch (IOException e) {
                System.out.println("Closing streams failed.");
            }
            try {
                if (fout != null)
                    fout.close();
            }
            catch (IOException e) {
                System.out.println("Closing streams failed.");
            }
        }
    }

    public static class RecentFileEntry {

        private String fileName;
        private String absolutePath;

        public RecentFileEntry(String absolutePath) {
            this.absolutePath = absolutePath;
            int lastIndex = absolutePath.lastIndexOf(File.separatorChar);

            this.fileName = (lastIndex == -1 ? absolutePath
                    : absolutePath.substring(lastIndex + 1, absolutePath.length()));
        }

        public String getAbsolutePath() {
            return absolutePath;
        }

        public String getFileName() {
            return fileName;
        }

        @Override
        public String toString() {
            return fileName;
        }

    }
}
