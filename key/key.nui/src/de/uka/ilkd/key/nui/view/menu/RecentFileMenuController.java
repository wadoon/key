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
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.Debug;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

/**
 * A {@link Menu} filled with recently opened files.
 * 
 * @author Nils Muzzulini
 * @version 1.0
 */
public class RecentFileMenuController extends ViewController {

    /**
     * Handles clicks on a menu item -> loads the file into the
     * {@link KeYMediator}.
     */
    private EventHandler<ActionEvent> menuItemClickedEventHandler;

    @FXML
    private Menu menu;

    /**
     * List of recent files.
     */
    private HashMap<MenuItem, RecentFileEntry> recentFiles;

    /**
     * Create a new RecentFiles list.
     * 
     * @param mediator
     *            {@link KeYMediator} to load files into
     */
    public void init(final KeYMediator mediator) {
        this.recentFiles = new LinkedHashMap<MenuItem, RecentFileEntry>();

        menuItemClickedEventHandler = new EventHandler<ActionEvent>() {

            @Override
            public void handle(ActionEvent event) {
                mediator.getUI().loadProblem(new File(getAbsolutePath((MenuItem) event.getSource())));
            }

        };

        menu.setDisable(menu.getItems().size() == 0);

        load(PathConfig.getRecentFileStorage());
    }

    /**
     * Removes a {@link MenuItem} from the recent file menu.
     * 
     * @param item
     *            MenuItem to be removed from the HashMap
     * @param index
     *            index of the MenuItem to be removed from the {@link Menu
     *            recent file menu}
     */
    private void removeFromModelAndView(MenuItem item, int index) {
        recentFiles.remove(item);
        menu.getItems().remove(index);
    }

    /**
     * Adds a file name to the {@link Menu} and the HashMap containing the
     * {@link MenuItem MenuItems}.
     * 
     * @param name
     *            name of the MenuItem
     */
    private void addToModelAndView(final String name) {
        final RecentFileEntry entry = new RecentFileEntry(name);
        if (new File(entry.getAbsolutePath()).exists()) {
            MenuItem item = new MenuItem(entry.getFileName());
            recentFiles.put(item, entry);
            menu.getItems().add(0, item);
            item.setOnAction(menuItemClickedEventHandler);
        }
    }

    /**
     * Returns the absolute path to the given {@link MenuItem}.
     * 
     * @param item
     *            {@link MenuItem}
     * @return absolute path to the MenuItem
     */
    private String getAbsolutePath(MenuItem item) {
        return recentFiles.get(item).getAbsolutePath();
    }

    /**
     * Call this method to add a new file to the beginning of the RecentFiles
     * list. If the name is already part of the list, it will be moved to the
     * first position. No more than a specified maximum number of names will be
     * allowed in the list, and additional names will be removed at the end.
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
        if (menu.getItems().size() == NUIConstants.MAX_RECENT_FILES) {
            removeFromModelAndView(menu.getItems().get(menu.getItems().size() - 1), menu.getItems().size() - 1);
        }
        addToModelAndView(name);
        menu.setDisable(menu.getItems().size() == 0);
    }

    /**
     * Put the names of the recent Files into the properties object. The
     * property names are "RecentFile0" "RecentFile1" ... The values are fully
     * qualified path names.
     * 
     * @param p
     *            {@link Properties}
     */
    private void store(Properties p) {
        // if there's nothing to store:
        for (int i = 0; i < menu.getItems().size(); i++) {
            p.setProperty("RecentFile" + i, getAbsolutePath(menu.getItems().get(i)));
        }
    }

    /**
     * Read the recent files from the given properties file.
     * 
     * @param filename
     *            path to the {@link Properties} file
     */
    private final void load(String filename) {
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
                System.out.println("Closing properties stream failed.");
            }
        }
    }

    /**
     * Write the recent file names to the given properties file. The file will
     * be read (if it exists) and then re-written so no information will be
     * lost.
     * 
     * @param filename
     *            path to the {@link Properties} file
     */
    public void store(String filename) {
        File localRecentFiles = new File(filename);
        FileInputStream fin = null;
        FileOutputStream fout = null;
        Properties p = new Properties();
        if (!localRecentFiles.getParentFile().exists()) {
            System.out.println("Oops. No folder to save recentFileList to.");
            return;
        }
        try {
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

    /**
     * Model of a recent file entry.
     * 
     * @author Nils Muzzulini
     * @version 1.0
     */
    public static class RecentFileEntry {

        private String fileName;
        private String absolutePath;

        /**
         * Constructs a new recent file entry.
         * 
         * @param absolutePath
         *            absolute path to the file entry
         */
        public RecentFileEntry(String absolutePath) {
            this.absolutePath = absolutePath;
            int lastIndex = absolutePath.lastIndexOf(File.separatorChar);

            this.fileName = (lastIndex == -1 ? absolutePath
                    : absolutePath.substring(lastIndex + 1, absolutePath.length()));
        }

        /**
         * @return the absolute path to the file entry
         */
        public String getAbsolutePath() {
            return absolutePath;
        }

        /**
         * @return name of the file entry
         */
        public String getFileName() {
            return fileName;
        }

        @Override
        public String toString() {
            return fileName;
        }

    }
}
