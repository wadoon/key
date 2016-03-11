/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import javafx.scene.control.TreeItem;

/**
 * @author Maximilian Li
 *
 */
public class XmlReader {
    private File inputFile;
    private List<String> selectorList = new ArrayList<>();
    private Map<String, String> descriptionMap = new HashMap<>();
    private TreeItem<String> treeRoot = new TreeItem<>("root");
    private Map<String, String> classMap = new HashMap<>();
    private Map<String, Boolean> classEnabledMap = new HashMap<>();

    /**
     * 
     */
    public XmlReader(String path, List<CssRule> ruleList) {
        inputFile = new File(path);
        for (CssRule rule : ruleList) {
            selectorList.addAll(rule.getSelectors());
        }
        handleFile();
    }

    public void handleFile() {
        try {
            DocumentBuilderFactory dbFactory = DocumentBuilderFactory
                    .newInstance();
            DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
            Document doc = dBuilder.parse(inputFile);
            doc.getDocumentElement().normalize();
            NodeList nList = doc.getElementsByTagName("TreeItem");

            for (int i = 0; i < nList.getLength(); i++) {
                Node node = nList.item(i);
                TreeItem<String> categoryNode = new TreeItem<String>(
                        ((Element) node).getAttribute("text"));
                NodeList childList = node.getChildNodes();

                for (int j = 0; j < childList.getLength(); j++) {
                    Node child = childList.item(j);
                    if (child.getNodeType() == Node.ELEMENT_NODE) {
                        Element elem = (Element) child;
                        String selector = elem.getElementsByTagName("selector")
                                .item(0).getTextContent();
                        if (selectorList.contains(selector)) {
                            selectorList.remove(selector);

                            String description = elem
                                    .getElementsByTagName("Description").item(0)
                                    .getTextContent();

                            descriptionMap.put(selector, description);

                            String className = elem
                                    .getElementsByTagName("Class").item(0)
                                    .getTextContent();

                            classMap.put(className, selector.substring(1));

                            classEnabledMap.put(className,
                                    elem.getElementsByTagName("enabled").item(0)
                                            .getTextContent().equals("true"));

                            TreeItem<String> childNode = new TreeItem<String>(
                                    description);
                            categoryNode.getChildren().add(childNode);

                        }
                    }

                }
                treeRoot.getChildren().add(categoryNode);
            }

        }
        catch (Exception e) {
            e.printStackTrace();
        }
        TreeItem<String> otherNode = new TreeItem<String>("Other");
        for (int i = 0; i < selectorList.size(); i++) {
            otherNode.getChildren()
                    .add(new TreeItem<String>(selectorList.get(i)));
        }
        treeRoot.getChildren().add(otherNode);
    }

    public TreeItem<String> getTree() {
        return treeRoot;
    }

    public Map<String, String> getDescriptionMap() {
        return descriptionMap;
    }

    public Map<String, String> getClassMap() {
        return classMap;
    }
    
    public Map<String, Boolean> getClassEnabledMap(){
        return classEnabledMap;
    }
}
