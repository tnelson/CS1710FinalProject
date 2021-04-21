//Get all the data out of Sterling
var stage =  document.getElementsByClassName("script-stage")[1];
const allinst = instances.map(instanceToGraph)
const numinst = instances.length - 1
var maindiv = getElem("stagediv","div")
stage.appendChild(maindiv); 

const clear = () => maindiv.innerHTML = ''
clear()
function draw(indx) { 
var nextbtn = getElem("nextbtn","BUTTON")
nextbtn.innerHTML = "Next"
nextbtn.onclick = nextClick
var prevbtn = getElem("prevbtn","BUTTON")
prevbtn.innerHTML = "Prev"
prevbtn.onclick = prevClick
var statebtn = getElem("statebtn","BUTTON")
statebtn.innerHTML = indx
maindiv.appendChild(prevbtn)
maindiv.appendChild(nextbtn)
maindiv.appendChild(statebtn)
var e = getElem("proctable","table")
maindiv.appendChild(e) ; 
createInstTable(allinst[indx])
}
draw(0) ; 
function getElem(eid,tp) { 
  var el = document.getElementById(eid) ; 
  if(!el) {
    el = document.createElement(tp) 
    el.id = eid
  }
  return el ; 
}
function nextClick() {
  const nextst = parseInt(getElem("statebtn","BUTTON").innerHTML) + 1
  if(nextst <= numinst) { 
  clear()
  draw(nextst)
  }
}
function prevClick() { 
  const prevst =parseInt(getElem("statebtn","BUTTON").innerHTML) - 1
  if(prevst >= 0 ) {
  clear()
  draw(prevst)
  }

}

function createInstTable(inst) { 
    let table = document.querySelector("table");
  table.style.border = "1px solid #000"
  table.style.padding = "10px"

    function generateTableHead(table) {
      var tableheaders = ["Process ID","Process","State","PageTable","Pages"]
      let thead = table.createTHead();
      let row = thead.insertRow();
      for (let key of tableheaders) {
      let th = document.createElement("th");
      let text = document.createTextNode(key);
      th.appendChild(text);
      row.appendChild(th);
      }
}
     generateTableHead(table)
    function createProcTable(proc) { 
      const data =  ["proc_id","pname","proc_state","proc_tbl","perms"]

  
    let row = table.insertRow();
      row.style.height = "150px"
    for (key of data) {
      let cell = row.insertCell();
      cell.style.border = "1px solid #000"
      let text = document.createTextNode(proc[key]);
      cell.appendChild(text);
    }
  
}
  inst.process.sort(sortById).map(createProcTable)
    
    }
function sortById(a,b) { 
a = parseInt(a.proc_id)
b = parseInt(b.proc_id)
if(a < b ) return -1
if (a > b) return 1 
  return 0

}




function instanceToGraph(inst) { 
  //The States 
  const states = inst.signature("State").atoms(true) ; 
const procs = inst.signature('Process').atoms(true) ;
  const pages = inst.signature("Page").atoms() ; 
  const pagetables = inst.signature('Pagetable').atoms() ; 
  //Process fields 
  const pid = inst.field('pid') ; 
  const proc_ptb  = inst.field('ptable') ; 
  const proc_st = inst.field('st') ; 
  //Pagetable fields
  const mapping = inst.field('mapping') ; 
  const permissions = inst.field('permissions') ; 
  //Page fields 
  const padr = inst.field("address") ; 
  const next = inst.field("next") ; 
  function getProcess(p) { 
    const prpg = p.join(proc_ptb).join(mapping).tuples().map(e => {return e.atoms()[0].id()})
                .reduce((a,v) => a +"," + v,"")  
    const perms = p.join(proc_ptb.join(permissions)).tuples().map(e => {return [e.atoms()[0].id(),e.atoms()[1].id()]})
                  .map(e => "(" + e[0] +","+e[1]+"),").reduce((a,v) => a + "\n " + v , "")
                                                          
    
    return {
    pname : p.id() , 
    proc_id : p.join(pid).tuples()[0].atoms()[0].id() , 
    proc_tbl : p.join(proc_ptb).tuples().map(e => {return e.atoms()[0].id()}).reduce((a,v) => a + " " + v , "") , 
    proc_pages: prpg , 
    perms: perms,
    proc_state: p.join(proc_st).tuples().map(e => {return e.atoms()[0].id()}).reduce((a,v) => a + " " + v , "")
  }
  }
  const allprocs = procs.map(getProcess) ; 
  function getPages(mp) {
    const pgdr = mp.atoms()[1].id()  ; 
    const pgArr = new Array() ; 
    for(const proc of allprocs) { 
      if(proc.proc_pages.includes(pgdr) ){
        pgArr.push(proc.pname)
      }
    }
    return {
      pagename:mp.atoms()[0].id(),
      addr: pgdr ,
      page_procs:pgArr
    }
  }
  const pgs = padr.tuples().map(getPages) ; 
  return {
    process:allprocs,
    pages:pgs
  } 
  
}