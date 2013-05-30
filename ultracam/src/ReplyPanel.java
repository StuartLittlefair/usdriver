package warwick.marsh.ultracam;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JFrame;
import javax.swing.JTextArea;
import javax.swing.JTextPane;
import javax.swing.JButton;
import javax.swing.JTree;
import javax.swing.JTabbedPane;
import javax.swing.border.LineBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.Color;
import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.awt.Dimension;

import java.util.Date;
import java.text.DateFormat;

import org.w3c.dom.Comment;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Text;

import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import warwick.marsh.util.*;

/**
 * Class that displays the server replies that result from various HTTP calls
 *
 */

public class ReplyPanel extends JPanel {

    public static final String XML_TREE_VIEW = "Tree view";
    public static final String XML_TEXT_VIEW = "Parameter view";

    private static final String HTML_ERROR   = "\"red\"";
    private static final String HTML_WARNING = "\"#FFA500\"";
    
    private DefaultMutableTreeNode _replyTreeRoot = new DefaultMutableTreeNode();
    private JTree   _replyTree                    = new JTree(new DefaultMutableTreeNode());
    private JTextPane _replyTextPane              = new JTextPane();
    
    StringBuffer _replyTextBuffer = new StringBuffer();
    
    public ReplyPanel() {

	super(new CardLayout());

	_replyTextPane.setEditable(false);
	_replyTextPane.setContentType("text/html");
	
	this.add(new JScrollPane(_replyTextPane, JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED), 
		 XML_TEXT_VIEW);
	this.add(new JScrollPane(_replyTree, JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED),    
		 XML_TREE_VIEW);

	this.setPreferredSize(new Dimension(400, 100));

    }
    
    public void showReply(Document document, String description, boolean reset) {

	// print to terminal
	try{
	    TransformerFactory tranFactory = TransformerFactory.newInstance();
	    Transformer       aTransformer = tranFactory.newTransformer();

//		System.out.println("------------------------- Start of XML from server ----------------------------------\n");
//		aTransformer.transform(new DOMSource(document), new StreamResult(System.out));
//		System.out.println("\n-------------------------  End of XML from server  ----------------------------------");
	}
	catch(Exception e){
	    System.err.println(e);
	}

	TreeDomNode rootTreeNode = new TreeDomNode(true);
	domNodeToTree(document, rootTreeNode, true);
	
	// Get rid of two top level root nodes.
	rootTreeNode = (TreeDomNode)rootTreeNode.getFirstChild();
	rootTreeNode = (TreeDomNode)rootTreeNode.getFirstChild();
	
	_updateTree(rootTreeNode, description, reset);
	_updateText(document, description, reset);
    }

    public static void domNodeToTree(Node domNode, TreeDomNode parentTreeNode, boolean displayNodeValue) {

	if(domNode instanceof Text) return;
	
	TreeDomNode treeNode = new TreeDomNode(domNode, displayNodeValue);
	
	parentTreeNode.add(treeNode);
	
	NamedNodeMap attributeNodes = domNode.getAttributes();
	
	if((attributeNodes != null) && (attributeNodes.getLength() > 0)) {
	    
	    for(int i = 0; i < attributeNodes.getLength(); i++) {
		treeNode.add(new TreeDomNode(attributeNodes.item(i), displayNodeValue));
	    }
	}
	
	
	NodeList childNodes = domNode.getChildNodes();
	
	if((childNodes != null) && (childNodes.getLength() > 0)) {
	    
	    for(int i = 0; i < childNodes.getLength(); i++)
		domNodeToTree(childNodes.item(i), treeNode, displayNodeValue);
	}
    }
    
    /**
     * Makes the reply tree rootTreeNode a subtree of the
     * root of model of the JTree of this class.
     */
    private void _updateTree(TreeDomNode rootTreeNode, String description, boolean reset) {
	// Remove all but the permanent root of model of the JTree of this
	// ReplyPanel class.
	if(reset)
	    _replyTreeRoot = new DefaultMutableTreeNode();
	
	// Create a description node and add the root node of the reply tree to it.
	DefaultMutableTreeNode descriptionNode = new DefaultMutableTreeNode(description);
	
	descriptionNode.add(rootTreeNode);
	
	// Add the description node to the permanent root of model of the JTree of this
	// ReplyPanel class.
	_replyTreeRoot.add(descriptionNode);
	
	_replyTree.setModel(new DefaultTreeModel(_replyTreeRoot));
	
	for(int i = 0; i < _replyTree.getRowCount(); i++)
	    _replyTree.expandRow(i);
	
    }
    
    private void _updateText(Document document, String description, boolean reset) {

	if(reset) 
	    _replyTextBuffer.setLength(0);
	
	String sourceName = "";
	
	// OK, WARNING, ERROR, BUSY, IDLE, UNKNOWN
	String nodeValue = "";
	
	// Used to find camera server, filesave server
	String nodeName = "";
	
	try {
	    Node sourceNode = document.getElementsByTagName("source").item(0);
	    sourceName = TreeDomNode.getNodeValue(sourceNode);
	    
	    // Use only the first word as source name:
	    try {
		sourceName = sourceName.substring(0, sourceName.indexOf(" "));
	    }
	    catch(Exception e) {
		System.out.println(e);
	    }
	}
	catch(Exception e) {
	    sourceName = "Unknown source";
	}
	
	_replyTextBuffer.append("<u>" + description + "</u>");
	
	_replyTextBuffer.append("<table>");
	
	try {
	    Node statusNode = document.getElementsByTagName("status").item(0);
	    NamedNodeMap statusAttributes = statusNode.getAttributes();
	    
	    for(int i = 0; i < statusAttributes.getLength(); i++) {
		nodeName = statusAttributes.item(i).getNodeName().trim();
		nodeValue = statusAttributes.item(i).getNodeValue();
		
		if(nodeName.equalsIgnoreCase("camera") || (nodeName.equalsIgnoreCase("software"))) {
		    if(nodeValue != null) {
			if(nodeValue.trim().equalsIgnoreCase("WARNING")) {
			    _replyTextBuffer.append("<tr bgcolor=" + HTML_WARNING + ">");
			}else if(nodeValue.trim().equalsIgnoreCase("ERROR")) {
			    _replyTextBuffer.append("<tr bgcolor=" + HTML_ERROR + ">");
			}else{
			    _replyTextBuffer.append("<tr>");
			}
		    }
		    
		    _replyTextBuffer.append("<td><i><b>" + sourceName + "</b></i></td><td>" + nodeName + "</td><td>" + nodeValue + "</td></tr>\n");
		}
	    }
	}
	catch(Exception e) {
	    _replyTextBuffer.append(sourceName + ": no status information");
	}
	
	try {
	    Node statusNode = document.getElementsByTagName("state").item(0);
	    NamedNodeMap statusAttributes = statusNode.getAttributes();
	    
	    for(int i = 0; i < statusAttributes.getLength(); i++) {
		nodeName = statusAttributes.item(i).getNodeName().trim();
		nodeValue = statusAttributes.item(i).getNodeValue();
		
		if(nodeName.equalsIgnoreCase("camera") || (nodeName.equalsIgnoreCase("software"))) {
		    if(nodeValue != null) {
			if(nodeValue.trim().equalsIgnoreCase("WARNING")) {
			    _replyTextBuffer.append("<tr bgcolor=" + HTML_WARNING + ">");
			}
			else if(nodeValue.trim().equalsIgnoreCase("ERROR")) {
			    _replyTextBuffer.append("<tr bgcolor=" + HTML_ERROR + ">");
			}
			else {
			    _replyTextBuffer.append("<tr>");
			}
		    }
		    
		    _replyTextBuffer.append("<td>" + sourceName + "</td><td>" + nodeName + "</td><td>" + nodeValue + "</td></tr>\n");
		}
	    }
	    
	    _replyTextBuffer.append("</table><hr>\n");
	    
	}
	catch(Exception e) {
	    _replyTextBuffer.append(sourceName + ": no state information");
	}
	
	_replyTextPane.setText(_replyTextBuffer.toString());
    }
    
    public void setTreeView(boolean treeView){
	if(treeView)
	    ((CardLayout)this.getLayout()).show(this, XML_TREE_VIEW);
	else
	    ((CardLayout)this.getLayout()).show(this, XML_TEXT_VIEW);
    }
}

