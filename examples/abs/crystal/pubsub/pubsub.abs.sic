module Pubsub;

data News = E1 | E2 | E3 | E4 | E5 | None;

//////////////////////////////////////////////////////////////
/////////////////////// INTERFACE ////////////////////////////
//////////////////////////////////////////////////////////////	

interface ServiceI{
	Unit subscribe(ClientI cl);
	Unit produce(Bool b1, Bool b2);
}

interface ProxyI{
	ProxyI add(ClientI cl);
	Unit publish(Fut<News> fut);
}

interface ProducerI{
	News detectNews();
}

interface NewsProducerI{
	Unit add(News ns);
	News getNews();
	List<News> getRequests();	
}

interface ClientI{
	Unit signal(News ns);
}


//////////////////////////////////////////////////////////////
///////////////////////// CLASS //////////////////////////////
//////////////////////////////////////////////////////////////

class Service(Int limit, NewsProducerI np) implements ServiceI{
	ProducerI prod; ProxyI proxy; ProxyI lastProxy;
	
	{prod = new Producer(np); proxy = new Proxy(limit,this); lastProxy = proxy; this!produce(True,True);}
	
	Unit subscribe(ClientI cl){lastProxy = lastProxy.add(cl);}
	
	Unit produce(Bool b1, Bool b2){Fut<News> fut = prod!detectNews(); proxy!publish(fut);}
}

class Proxy(Int limit, ServiceI s) implements ProxyI{
	List<ClientI> myClients = Nil; ProxyI nextProxy; 
	
	ProxyI add(ClientI cl){
		ProxyI lastProxy = this;
		if(length(myClients) < limit){myClients = appendright(myClients, cl);}
		else{
			if(nextProxy == null){
 			   Future<ProxyI> tmpNextProxy = new Proxy(limit,s);
			   nextProxy = tmpNextProxy.get();
			}
			lastProxy = nextProxy!add(cl);
		}

		return lastProxy;
	}
	
	Unit publish(Fut<News> fut){
		Int counter = 0; News ns = None;
		
		ns = fut.get;	
		while(counter < length(myClients)){
			ClientI client = nth(myClients, counter);
			client!signal(ns);
			counter = counter + 1;
		}		
			
		if(nextProxy == null){s!produce(True,True);}
		else{nextProxy!publish(fut);}
	}
}

class Producer(NewsProducerI np) implements ProducerI{	
	News detectNews(){
		List<News> requests = Nil;
	    	News ns = None;
		requests =  np!getRequests();
		while(requests == Nil){
		  Future<List<News>> tmpRequests =  np!getRequests();
		  requests = tmpRequests.get();
		}
		Future<News> tmpns = np!getNews();
		ns = tmpns.get();
		return ns;
	}
}

class NewsProducer implements NewsProducerI{
	List<News> requests = Nil;
	
	Unit add(News ns){
		requests = appendright(requests,ns);
	}
	
	News getNews(){
		News firstNews = head(requests);
		requests = tail(requests);
		return firstNews;
	}
	
	List<News> getRequests(){
		return requests;
	}
}

class Client implements ClientI{
	News event = None;
	
	Unit signal(News ns){
		event = ns;
	}
}


{
	NewsProducerI np = new  NewsProducer();	
	ServiceI service = new Service(3,np);
	
	ClientI client1 = new Client(); service!subscribe(client1);
	ClientI client2 = new Client(); service!subscribe(client2);
	np!add(E1);
	ClientI client3 = new Client(); service!subscribe(client3);
	np!add(E2);	
	ClientI client4 = new Client(); service!subscribe(client4);	
	np!add(E3);	
}
