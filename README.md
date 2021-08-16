# Verifying Basic OS Memory Properties 

The Operating System is the fundamental core of all modern computing devices. It handles memory allocation for the hundreds of processes that run concurently on a modern machine. It is critical that this works perfectly with no bugs for two primary reasons:

1. Safety: Any error in kernel code or memory management renders any notion of security irrelevant. It is critical that memory isolation and security is strictly enforced
2. Correctness : Errors at the kernel level make building reliable code immensely difficult if not impossible

## Our Model
Due to the immense scope of the problem we take a very abstract view and model only certain specific operations. Our model can 
be thought to repersent a primitive OS that runs on a single core machine. 

Fundamentally our model consists of two parts:
1. Processes : Programs that run on the machine. They are of two types : UserProcesses which are sandboxed and the Kernel process which runs in privelaged mode and is all powerful. The Kernel process is initialized at startup, whereas UserProcesses may be initialized and delted at any time.
2. Memory : We model memory in the form of pages. Each process is initialized with a constant number of pages. In particular, kernel space has 3 static pages and user processes are initialized with 2 pages (representing, perhaps, the code, data, and stack). UserProcesses may allocate and free memory (much like heap memory is allocated and freed to/from processes) at any time (this includes the initially allocated pages).

On top of this we have pagetables which map virtual memory, states which capture each processes's fundamental state. 
Notably we implemented and verified several key properties. Among our successes we count:
1. We implemented and verified overlapping virtual memory address spaces
2.We verified memory isolation between processes 
3.We verified the safety of the process lifecyle 

### Visualisation
Our visualisation is a basic HTML table that displays what can be thought of as each process's ``descriptor", namely, it's state, VA mappings, and permissions.

This is also an added benefit of our model. It provides a clear and simple way to understand a complex topic that is often confusing.

## Limitations 
We do not consider several key parts of a modern OS : 
1.We neglect registers 
2.We do not consider multithreading
3.We do not model memory access (What happens when a process acceses an adress in it's VA space that has not been allocated)
4. We do not consider process forking 
This is a small subset of things we do not consider among a modern OS's powerful feature set. Indeed even the most cutting edge 
research in the world cannot fully model/verify something as expansive as the Linux kernel.  
##Tradeoffs
Due to the fact that we use pages to represent our basic unit of memory we are unable to capture byte level memory errors (such as overwrites) with our model. 
