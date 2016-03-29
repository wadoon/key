package de.uka.ilkd.key.nui.view.menu;

import java.util.HashMap;
import java.util.Map;

import org.key_project.util.reflection.ClassLoaderUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.util.ProofMacroWorker;
import de.uka.ilkd.key.proof.Node;
import javafx.fxml.FXML;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

/**
 * Copied from ProofMacroMenu and adapted to JavaFX style. This is NOT a menu
 * anymore but a view controller. There is a field rootMenu to access the actual
 * menu.
 * 
 * @see de.uka.ilkd.key.gui.ProofMacroMenu
 * @author Victor Schuemmer
 */
public class ProofMacroMenuController extends ViewController {

    @FXML
    private Menu rootMenu;

    /**
     * The loader used to access the providers for macros.
     *
     * This is used as iteration source in other parts of KeY's ui.
     */
    public static final Iterable<ProofMacro> REGISTERED_MACROS = ClassLoaderUtil
            .loadServices(ProofMacro.class);

    /**
     * Use this method to pass additional Information that would normally given
     * to the constructor.
     * 
     * @param posInOcc
     *            the {@link PosInOccurrence} where this menu is requested.
     */
    // XXX any possibility to get rid of this?
    public void init(PosInOccurrence posInOcc) {
        // Macros are grouped according to their category.
        // Store the sub menus in this map.
        Map<String, Menu> submenus = new HashMap<String, Menu>();

        Node node = getContext().getKeYMediator().getSelectedNode();
        for (ProofMacro macro : REGISTERED_MACROS) {

            boolean applicable = node != null
                    && macro.canApplyTo(node, posInOcc);

            // NOTE (DS): At the moment, JoinRule is an experimental
            // feature. We therefore only add join-related macros
            // if the feature is currently active.
            // TODO (DS): Remove below check related to the exp. \\
            // feature once JoinRule is considered stable.
            if (!Main.isExperimentalMode()
                    && macro.getName().contains("join")) {
                applicable = false;
            }

            if (applicable) {
                MenuItem menuItem = createMenuItem(macro, posInOcc);

                String category = macro.getCategory();
                Menu submenu = rootMenu;
                if (category != null) {
                    submenu = submenus.get(category);
                    if (submenu == null) {
                        submenu = new Menu(category);
                        submenus.put(category, submenu);
                        rootMenu.getItems().add(submenu);
                    }
                }

                submenu.getItems().add(menuItem);
            }
        }
    }

    /**
     * Creates a menu item for the given {@link ProofMacro}.
     * 
     * @param macro
     *            the macro to create an item for
     * @param posInOcc
     *            the {@link PosInOccurrence} where the menu has been requested.
     * @return a menu item that executes the given macro, with the macro's name
     *         as text.
     */
    private MenuItem createMenuItem(final ProofMacro macro,
            final PosInOccurrence posInOcc) {

        MenuItem menuItem = new MenuItem(macro.getName());
        KeYMediator mediator = getContext().getKeYMediator();

        menuItem.setOnAction(e -> {
            if (mediator.isInAutoMode()) {
                return;
            }
            final ProofMacroWorker worker = new ProofMacroWorker(macro,
                    mediator, posInOcc);
            mediator.stopInterface(true);
            mediator.setInteractive(false);
            mediator.addInterruptedListener(worker);
            new Thread(worker).start();
        });

        return menuItem;
    }

}
