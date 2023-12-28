use std::{io, fmt, cmp, iter};
use itertools::iproduct;
use std::time::{Duration, Instant};

use std::collections::{HashSet, VecDeque, HashMap};

macro_rules! parse_input {
    ($x:expr, $t:ident) => ($x.trim().parse::<$t>().unwrap())
}

const MAX_DRONES: usize = 4;
const MAX_SCANS: usize = 10;
const MAX_CREATURES: usize = 22;
const GRID_MAX_X: usize = 100;
const GRID_MAX_Y: usize = 100;

const D_MONSTER_EMER: f64 = 500.0;
const MONSTER_SPEED_ANGRY: i32 = 540;
const D_MAX_DRONE: i32 = 600;
const D_GRID_MAX_DRONE: i32 = D_MAX_DRONE/GRID_MAX_X as i32;

const LIGHT_STD: i32 =  800;
const LIGHT_UPDATED: i32 =  2000;
const GRID_LIGHT_STD: i32 = LIGHT_STD / GRID_MAX_X as i32;

const BOARD_MAX_X: usize = 10000;
const BOARD_MAX_Y: usize = 10000;

/*fn go_dir(dir: &RadarDir) -> Point {
    match dir {
	RadarDir::BL => Point {x:0,y:10000},
	RadarDir::TL => Point {x:0,y:0},
	RadarDir::BR => Point {x:10000, y:10000},
	RadarDir::TR => Point {x:10000, y:0},
    }
}*/

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GridPoint { 
    x:i32,
    y:i32,
}
impl fmt::Display for GridPoint {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	fmt.write_str(&format!("gr({}, {})",self.x,self.y))?;
        Ok(())
    }
}

impl GridPoint {
    fn dist(p1: &GridPoint, p2: &GridPoint) -> f64 {
	let dx = f64::from(p1.x - p2.x);
	let dy = f64::from(p1.y - p2.y);
	(dx * dx + dy * dy).sqrt()
    }
    fn de_gridify(&self) -> Point {
	Point {x:self.x * GRID_MAX_X as i32, y:self.y * GRID_MAX_Y as i32}
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Point { 
    x:i32,
    y:i32,
}

impl fmt::Display for Point {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	fmt.write_str(&format!("({}, {})",self.x,self.y))?;
        Ok(())
    }
}

impl Point {
    fn dist(p1: &Point, p2: &Point) -> f64 {
	let dx = f64::from(p1.x - p2.x);
	let dy = f64::from(p1.y - p2.y);
	(dx * dx + dy * dy).sqrt()
    }
    fn gridify(&self) -> GridPoint {
	GridPoint {x:(self.x as f32/GRID_MAX_X as f32).floor() as i32, y:(self.y as f32/GRID_MAX_Y as f32).floor() as i32}
    }

    fn div(&self, d_f:f64) -> Point{
	Point {x:(self.x as f64/d_f ) as i32, y:(self.y as f64 /d_f) as i32}
    }

    fn add(a: Point, b: Point) -> Point {
	Point { x: a.x + b.x, y: a.y + b.y }
    }

    fn sub(a: Point, b: Point) -> Point {
	Point { x: a.x - b.x, y: a.y - b.y }
    }

    fn dot(a: Point, b: Point) -> f64 {
	f64::from(a.x * b.x + a.y * b.y)
    }

    fn hypot2(a: Point, b: Point) -> f64 {
	Point::dot(Point::sub(a, b), Point::sub(a, b))
    }

    // Function for projecting some vector a onto b
    fn proj(a: Point, b: Point) -> Point {
	let k = Point::dot(a, b) / Point::dot(b, b);
	Point { x: (k * b.x as f64) as i32, y: (k * b.y as f64) as i32 }
    }

    fn distance_segment_to_point(a: Point, b: Point, c: Point) -> f64 {
	// Compute vectors AC and AB
	let ac = Point::sub(c, a);
	let ab = Point::sub(b, a);

	// Get point D by taking the projection of AC onto AB then adding the offset of A
	let d = Point::add(Point::proj(ac, ab), a);
	
	let ad = Point::sub(d, a);
	// D might not be on AB so calculate k of D down AB (aka solve AD = k * AB)
	// We can use either component, but choose larger value to reduce the chance of dividing by zero
	let k = if ab.x.abs() > ab.y.abs() { ad.x as f64 / ab.x as f64 } else { ad.y as f64/ ab.y as f64 };

	// Check if D is off either end of the line segment
	if k <= 0.0 {
            return (Point::hypot2(c, a)).sqrt();
	} else if k >= 1.0 {
            return (Point::hypot2(c, b)).sqrt();
	}

	(Point::hypot2(c, d)).sqrt()
    }

    /// coord [AB], center circle, radius
    fn is_circle_line_collision(a: Point, b:Point, cc: Point, cr:i32) -> bool {
	Point::distance_segment_to_point(a,b,cc) as i32 <= cr
    }
}


#[derive(Debug, PartialEq, Clone, Copy)]
enum MapLocation {
    T, // tout en haut
    H, // en haut
    M, // millieu
    B, // bas
    Mo, // monster
}

impl MapLocation {
    fn to_min_max_pts(ml: MapLocation) -> (Point, Point) {
	match ml {
	    MapLocation::T => (Point {x:0,y:0}, Point {x:BOARD_MAX_X as i32,y:2500}),
	    MapLocation::H => (Point {x:0,y:2500}, Point {x:BOARD_MAX_X as i32,y:5000}),
	    MapLocation::M => (Point {x:0,y:5000}, Point {x:BOARD_MAX_X as i32,y:7500}),
	    MapLocation::B => (Point {x:0,y:7500}, Point {x:BOARD_MAX_X as i32,y:10000}),
	    MapLocation::Mo => (Point {x:0,y:2500}, Point {x:BOARD_MAX_X as i32,y:10000}),
	}
    }
}

#[derive(Debug, Clone, Copy)]
enum RadarDir {
    TL, // : la créature est en haut à gauche du drone.
    TR, // : la créature est en haut à droite du drone.
    BR, // : la créature est en bas à droite du drone.
    BL, // : la créature est en bas à gauche du drone.
}

#[derive(Debug, Copy, Clone)]
struct FishDetail {
    color: i32,
    fish_type: i32,
}
impl FishDetail {
    fn get_zone(&self) -> MapLocation {
	match self.fish_type {
	    0 => MapLocation::H,
	    1 => MapLocation::M,
	    2 => MapLocation::B,
	    _ => MapLocation::Mo,
	}
    }
}

#[derive(Debug, Clone, Copy)]
struct Fish {
    fish_id: i32,
    pos: Point,
    pos_prev: Option<Point>, //for the monster, need the previous
    speed: Point,
    detail: FishDetail,
}

#[derive(Debug, Clone)]
struct RadarBlip {
    fish_id: i32,
    fish_detail: FishDetail,
    dir: RadarDir,
}

#[derive(Debug, Clone)]
struct Drone {
    drone_id: i32,
    pos: Point,
    emergency: bool,
    battery: i32,
    scans: Vec<i32>,
    radars: Option<Vec<RadarBlip>>,
    prev_action: Option<Action>,
}

impl Drone {
    fn where_i_am(&self) -> MapLocation {
	if self.pos.y < 2500 {
           return MapLocation::T;
	}
	else if  self.pos.y < 5000 {
            return MapLocation::H;
	}
	else if self.pos.y < 7500 {
            return MapLocation::M;
	}
	else {
            return MapLocation::B;
	}
    }
}

#[derive(Debug, Clone)]
struct Board {
    my_score: i32,
    opp_score: i32,
    
    my_scans: Vec<i32>,
    opp_scans: Vec<i32>,

    my_drones: Vec<Drone>,
    opp_drones: Vec<Drone>,

    visible_fishes: Vec<Fish>,

    grid_sliced: [Option<GridSlice>; MAX_CREATURES],
}

impl Board {
    fn from_input_board(ib: &InputlBoard) -> Board {
	let mut tab_creat :[Option<GridSlice>; MAX_CREATURES] = [None; MAX_CREATURES];
	
	for d in ib.my_drones.iter().chain(ib.opp_drones.iter()) {
	    let gs = GridSlice::from_unique_pt(d.pos);
	    tab_creat[d.drone_id as usize] = Some(gs); 
	}

	//update based on radar

	
	for d in ib.my_drones.iter() {
	    //radar
	    for r in d.radars.as_ref().unwrap().iter() {
		let gs_r = GridSlice::from_radar(d.pos, r.dir);
		let gs_f = GridSlice::from_map_loc(r.fish_detail.get_zone());
		let inter = gs_r.intersec(gs_f);

		if let Some(gs_e) = &mut tab_creat[r.fish_id as usize] {
		    *gs_e = gs_e.intersec(inter);
		}
		else {
		  tab_creat[r.fish_id as usize] = Some(inter);  
		}		
	    }
	}

	for f in ib.visible_fishes.iter() {
	    eprintln!("visi fish {}", f.fish_id);
	    tab_creat[f.fish_id as usize] = Some(GridSlice::from_unique_pt(f.pos));
	}

	for (idx,i) in tab_creat.iter().enumerate() {
	    if let Some(it) = i {
		eprintln!("fid {} - {}", idx, it);
	    }
	}
	
	Board {my_score:ib.my_score, opp_score:ib.opp_score, my_scans:ib.my_scans.clone(), opp_scans: ib.opp_scans.clone(), my_drones:ib.my_drones.clone(), opp_drones:ib.opp_drones.clone(), visible_fishes:ib.visible_fishes.clone(), grid_sliced:tab_creat}
    }

    ///update monsters coordinate for next step
    fn update_monster(&self, fish: &mut Fish) {
	assert_eq!(fish.detail.fish_type, -1);

	eprintln!(" init p :{}, v {} id {}",fish.pos, fish.speed, fish.fish_id);
	fish.pos_prev = Some(fish.pos);
	//find minimum drone
	let (closest_dis, closest_dr) = self.my_drones.iter()
	    .chain(self.opp_drones.iter())
	    .map(|d| (Point::dist(&d.pos, &fish.pos), d))
	    .min_by(|x0,x1| x0.0.partial_cmp(&x1.0).unwrap())
	    .unwrap();

	eprintln!(" closest dist :{}, cd {:?}",closest_dis, closest_dr);

	
	let mut d_light = LIGHT_STD; //TODO change if light on

	if let Some(act) = closest_dr.prev_action {
	    match act {
		Action::MOVE(_, l) => { if l {d_light = LIGHT_UPDATED}},
		_ => (),
	    }
	}
	
	eprintln!("LIGHT : {}", d_light);
	if (closest_dis as i32) <= d_light {
	    //go to the direction of the drone

	    let v_abs = Point {x:closest_dr.pos.x - fish.pos.x, y: closest_dr.pos.y - fish.pos.y};
	    let (dx_n, dy_n) = ((MONSTER_SPEED_ANGRY as f64/closest_dis), ( MONSTER_SPEED_ANGRY as f64/closest_dis));
	    let p_new = Point {x:((v_abs.x as f64)*dx_n) as i32,y:((v_abs.y as f64)*dy_n) as i32};
	    fish.speed = p_new;
	    //eprintln!("pt ne {} old: {} grid {}, idx{} {} {}", p_new, p, dist, idx, dx_n, dy_n);
	    eprintln!("fspeed :{}", fish.speed);
	} 
	// only update pos (spped already updated before)
	fish.pos.x += fish.speed.x;
	fish.pos.y += fish.speed.y;

	fish.pos.x = cmp::min(cmp::max(0, fish.pos.x), (BOARD_MAX_X -1) as i32);
	fish.pos.y = cmp::min(cmp::max(2500, fish.pos.y), (BOARD_MAX_Y -1) as i32);

	eprintln!(" predicted p :{}, v {} id {}",fish.pos, fish.speed, fish.fish_id);
	
    }
    
    fn next_board(&self, acs: &Vec<Action>) -> Board {
	//focus on monster for now

	let mut out_b = self.clone();

	for f in out_b.visible_fishes.iter_mut() {
	    if f.detail.fish_type == -1 {
		self.update_monster(f);
	    }
	}
	
	out_b	
    }


    fn monster_collision(&self, ps: Point, pe:Point, pe_inter_long: Point, pe_inter_short: Point, dir_d: Point) -> bool {
	let mut coll_found = false;
	for f in self.visible_fishes.iter() {
	    if f.detail.fish_type == -1 {
		//check collision

		if Point::dot(f.speed, dir_d) >= 0.0 {
		    if Point::dist(&pe,&f.pos) <= D_MONSTER_EMER || Point::dist(&pe_inter_long,&f.pos) <= D_MONSTER_EMER{
			//eprintln!("COL1 {} {}",ps, pe);
			coll_found = true;
		    }
		} else {
		    if Point::dist(&pe,&f.pos) <= D_MONSTER_EMER || Point::dist(&pe_inter_short,&f.pos) <= D_MONSTER_EMER{
			//eprintln!("COL1 {} {}",ps, pe);
			coll_found = true;
		    }
		}
		if let Some(prev_p) = f.pos_prev {
		    //if Point::is_circle_line_collision(ps, pe, prev_p, 500) {
			if Point::dist(&pe,&prev_p) <= D_MONSTER_EMER { //|| Point::dist(&pe_inter,&prev_p) <= D_MONSTER_EMER{
			//eprintln!("COL2 {} {}",ps, pe);
			coll_found = true;
		    }
		}
	    }
	}
	coll_found
    }
    fn get_successor(&self, p:GridPoint) -> [Option<GridPoint>;8] {
	let mut ret_tab = [None;8];
	let mut idx = 0; // bug enumerae

	for (dx_a,dy_a) in iproduct!([-1,0,1], [-1,0,1]) {
	    if dx_a == 0 && dy_a == 0 {
		continue;
	    }
	    let dist = GridPoint::dist(&GridPoint {x:0,y:0} ,&GridPoint {x:dx_a,y:dy_a});
	    let (dx_n, dy_n) = ((D_GRID_MAX_DRONE as f64/dist), (D_GRID_MAX_DRONE as f64/dist));
	    let d_n_inter_long = ((D_GRID_MAX_DRONE as f64)/(2.0/3.0))/dist;
	    let d_n_inter_short = ((D_GRID_MAX_DRONE as f64)/(3.0))/dist;
	    let p_new = GridPoint {x:p.x + ((dx_a as f64)*dx_n) as i32,y:p.y + ((dy_a as f64)*dy_n) as i32};
	    let p_new_intermediate_l = GridPoint {x:p.x + ((dx_a as f64)*(d_n_inter_long)) as i32,y:p.y + ((dy_a as f64)*(d_n_inter_long)) as i32}; //to check intermediate col
	    let p_new_intermediate_s = GridPoint {x:p.x + ((dx_a as f64)*(d_n_inter_short)) as i32,y:p.y + ((dy_a as f64)*(d_n_inter_short)) as i32}; //to check intermediate col

	    
	    //eprintln!("pt ne {} inter {} dist: {}  idx{} {} {}", p_new, p_new_intermediate, dist, idx, dx_n, dy_n);
	    //eprintln!("deg  ne {} inter {} orig {}", p_new.de_gridify(), p_new_intermediate.de_gridify(),p.de_gridify()) ;

	    
	    if p_new.x < 0 || p_new.x >= GRID_MAX_X as i32|| p_new.y < 0 || p_new.y >= GRID_MAX_X as i32{
		continue;
	    }

	    if self.monster_collision(p.de_gridify(), p_new.de_gridify(),p_new_intermediate_l.de_gridify(), p_new_intermediate_s.de_gridify(),Point {x:dx_a,y:dy_a} ) {
		continue;
	    }
	    ret_tab[idx] = Some(p_new);
	    idx +=1;
	}

	if ret_tab.iter().filter(|v| v.is_some()).count() == 0 {
	    // only none
	    eprintln!("None onl s {} sdg {}", p, p.de_gridify());
	    for (dx_a,dy_a) in iproduct!([-1,0,1], [-1,0,1]) {
		if dx_a == 0 && dy_a == 0 {
		    continue;
		}
		let dist = GridPoint::dist(&GridPoint {x:0,y:0} ,&GridPoint {x:dx_a,y:dy_a});
		let (dx_n, dy_n) = ((D_GRID_MAX_DRONE as f64/dist), (D_GRID_MAX_DRONE as f64/dist));
		let d_n_inter = ((D_GRID_MAX_DRONE as f64)/2.0)/dist;
		let p_new = GridPoint {x:p.x + ((dx_a as f64)*dx_n) as i32,y:p.y + ((dy_a as f64)*dy_n) as i32};
		let p_new_intermediate = GridPoint {x:p.x + ((dx_a as f64)*(d_n_inter)) as i32,y:p.y + ((dy_a as f64)*(d_n_inter)) as i32}; //to check intermediate col
		//eprintln!("pt ne {} inter {} dist: {}  idx{} {} {}", p_new, p_new_intermediate, dist, idx, dx_n, dy_n);
		//eprintln!("deg  ne {} inter {} orig {}", p_new.de_gridify(), p_new_intermediate.de_gridify(),p.de_gridify()) ;
	    }
	}
	ret_tab
    }

   fn dfs(&self, si:Point, ei:Point) -> Option<Vec<Point>> {
	//use a dfs for this
       let s = si.gridify();
       let e = ei.gridify();
       
       eprintln!("dfs start {} end {} sg{} eg{}", si, ei, s, e);
       let mut visited :HashSet<GridPoint> = HashSet::new();
	visited.insert(s);
	
	let mut queue: VecDeque<(GridPoint, Vec<Point>)> = VecDeque::new();
	queue.push_back((s, vec![s.de_gridify()]));

	
	while !queue.is_empty() {
	    let (cur_pos, path) = queue.pop_front().unwrap();


	    for nei_try in self.get_successor(cur_pos) {
		if let Some(nei) = nei_try {
		    //eprintln!("cur_pos {} nei {} {} {}",cur_pos, nei, cur_pos.de_gridify(), nei.de_gridify());
		    if !visited.contains(&nei) {
			let new_vec:Vec<Point> =  path.iter().copied().chain(iter::once(nei.de_gridify())).collect();
			queue.push_back((nei, new_vec.clone()));
			visited.insert(nei);
			//if Point::dist(&nei,&e) < 400.0 {
			if GridPoint::dist(&e, &nei) < GRID_LIGHT_STD as f64 {
			    return  Some(new_vec.clone());
			}
		    }
		}
	    }
	}
	None
    }
}

#[derive(Debug)]
struct InputlBoard {
    my_score: i32,
    opp_score: i32,
    fish_details: HashMap<i32, FishDetail>,
    my_scans: Vec<i32>,
    opp_scans: Vec<i32>,

    my_drones: Vec<Drone>,
    opp_drones: Vec<Drone>,

    visible_fishes: Vec<Fish>,
    
  }


#[derive(Debug, Copy, Clone)]
enum Action { 
    MOVE(Point, bool), 
    WAIT(bool),
}


impl fmt::Display for Action {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
  	match self {
	    Action::MOVE(p, l) => fmt.write_str(&format!("MOVE {} {} {}",p.x,p.y,*l as i32))?,
	    Action::WAIT(l) => fmt.write_str(&format!("WAIT {}", l))?,
	}
        Ok(())
    }
}



#[derive(Debug, Copy, Clone)]
struct GridElem {
    creatures_proba :[f32; MAX_CREATURES],

    
}
/*#[derive(Debug)]
struct GridApprox {
    grid: [[GridElem; GRID_MAX_X]; GRID_MAX_Y],
    grid_sliced: [Option<GridSlice>; MAX_CREATURES],
    grid_path: [[bool; GRID_MAX_X]; GRID_MAX_Y],
    
}*/

#[derive(Debug, Clone, Copy)]
/// points are note in the gridified space !!
struct GridSlice {
    p_min: Point,
    p_max: Point,
    is_unique: bool,

}

impl fmt::Display for GridSlice {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	if self.is_unique {
	    assert_eq!(self.p_min, self.p_max);
	    assert_eq!(self.p_min, self.center());
	    assert_eq!(self.num_elems(), 1);
		
	    fmt.write_str(&format!("p: {} ** UNI **",self.p_min))?;
	} else {
	    fmt.write_str(&format!("p_min: {}, p_max: {} (center: {}) (sz {})",self.p_min,self.p_max, self.center(), self.num_elems()))?;
	}
        Ok(())
    }
}

impl GridSlice {
    /// num elems for the gridified slice
    fn num_elems(&self) -> i32 {
	if !self.is_unique {
	    let min_y = self.p_min.gridify().y as usize;
	    let min_x = self.p_min.gridify().x as usize;
	    let max_y = self.p_max.gridify().y as usize;
	    let max_x = self.p_max.gridify().x as usize;
	    ((max_x - min_x)*(max_y - min_y)) as i32
	} else {
	    // 1 if element unique
	    1
	}
		
    }

    fn from_tuple(pts: (Point, Point)) -> GridSlice {
	let (p_min, p_max) = pts;
	GridSlice {p_min, p_max, is_unique:false}
	
    }

    fn intersec(&self, gs:GridSlice) -> GridSlice {
	let min_y1 = self.p_min.y as usize;
	let min_x1 = self.p_min.x as usize;
	let max_y1 = self.p_max.y as usize;
	let max_x1 = self.p_max.x as usize;

	let min_y2 = gs.p_min.y as usize;
	let min_x2 = gs.p_min.x as usize;
	let max_y2 = gs.p_max.y as usize;
	let max_x2 = gs.p_max.x as usize;

	let min_x_n = cmp::max(min_x1, min_x2);
	let max_x_n = cmp::min(max_x1, max_x2);
	let min_y_n = cmp::max(min_y1, min_y2);
	let max_y_n = cmp::min(max_y1, max_y2);

	GridSlice {p_min: Point {x:min_x_n as i32, y:min_y_n as i32}, p_max: Point {x:max_x_n as i32, y:max_y_n as i32}, is_unique:false}
	
    }

    fn from_radar(d_pos: Point, r_dir: RadarDir) -> GridSlice {
	match r_dir {
	    RadarDir::BL => GridSlice {p_min: Point {x:0,y:d_pos.y}, p_max: Point {x:d_pos.x, y:BOARD_MAX_Y as i32}, is_unique:false},
	    RadarDir::BR => GridSlice {p_min: d_pos , p_max: Point {x:BOARD_MAX_X as i32,y:BOARD_MAX_Y as i32}, is_unique:false},
	    RadarDir::TL => GridSlice {p_min: Point {x:0,y:0}, p_max: d_pos, is_unique:false},
	    RadarDir::TR => GridSlice {p_min: Point {x:d_pos.x, y:0}, p_max: Point {x:BOARD_MAX_X as i32,y:d_pos.y}, is_unique:false},
	}
    }

    fn from_map_loc(ml: MapLocation) -> GridSlice {
	GridSlice::from_tuple(MapLocation::to_min_max_pts(ml))
    }
    fn from_unique_pt(pt: Point) -> GridSlice {
	GridSlice {p_max:pt, p_min:pt, is_unique:true }
    }

    fn center(&self) -> Point {
	if !self.is_unique {
	    Point {x:self.p_min.x + (self.p_max.x - self.p_min.x)/2, y:self.p_min.y + (self.p_max.y - self.p_min.y)/2}
	} else {
	    assert_eq!(self.p_min, self.p_max);
	    self.p_min
	}
    }
}





/**
 * Score points by scanning valuable fish faster than your opponent.
 **/
fn main() {

    //let ac = Action::MOVE(Point {x:54, y:44}, true);
	    
    //println!("{}", ac); // MOVE <x> <y> <light (1|0)> | WAIT <light (1|0)>

   

    let mut prev_action: [Option<Action>; MAX_DRONES] = [None; MAX_DRONES];
    
    let mut hash_fish = HashMap::new();
    
    let mut input_line = String::new();
    io::stdin().read_line(&mut input_line).unwrap();
    let creature_count = parse_input!(input_line, i32);
    for _ in 0..creature_count as usize {
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let inputs = input_line.split(" ").collect::<Vec<_>>();
        let creature_id = parse_input!(inputs[0], i32);
        let color = parse_input!(inputs[1], i32);
        let fish_type = parse_input!(inputs[2], i32);
	assert!(creature_id <= 21);
	hash_fish.insert(creature_id, FishDetail {color, fish_type});
    }

    // game loop
    let mut cur_step = 0;
    loop {
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let my_score = parse_input!(input_line, i32);
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let foe_score = parse_input!(input_line, i32);
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
	let mut my_scans = Vec::new();
        let my_scan_count = parse_input!(input_line, i32);
        for _ in 0..my_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let creature_id = parse_input!(input_line, i32);
	    my_scans.push(creature_id);
        }
	let mut opp_scans = Vec::new();
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let foe_scan_count = parse_input!(input_line, i32);
        for _ in 0..foe_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let creature_id = parse_input!(input_line, i32);
	    opp_scans.push(creature_id);
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();

	let mut my_drones= Vec::new();
        let my_drone_count = parse_input!(input_line, i32);
        for _ in 0..my_drone_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let drone_x = parse_input!(inputs[1], i32);
            let drone_y = parse_input!(inputs[2], i32);
            let emergency = parse_input!(inputs[3], i32);
            let battery = parse_input!(inputs[4], i32);
	    my_drones.push(Drone {drone_id:drone_id, pos:Point{x:drone_x,y:drone_y}, emergency:emergency==1,battery:battery,scans:Vec::new(),radars:Some(Vec::new()), prev_action:prev_action[drone_id as usize]});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
	let mut opp_drones= Vec::new();
        let foe_drone_count = parse_input!(input_line, i32);
        for _ in 0..foe_drone_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let drone_x = parse_input!(inputs[1], i32);
            let drone_y = parse_input!(inputs[2], i32);
            let emergency = parse_input!(inputs[3], i32);
            let battery = parse_input!(inputs[4], i32);
	    opp_drones.push(Drone {drone_id:drone_id, pos:Point{x:drone_x,y:drone_y}, emergency:emergency==1,battery:battery,scans:Vec::new(),radars:None, prev_action:None});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let drone_scan_count = parse_input!(input_line, i32);
        for _ in 0..drone_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let creature_id = parse_input!(inputs[1], i32);
	    opp_drones.iter_mut()
		.chain(my_drones.iter_mut())
		.find(|e| e.drone_id == drone_id)
		.unwrap()
		.scans.push(creature_id);
	    
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let visible_creature_count = parse_input!(input_line, i32);
	let mut visible_fishes = Vec::new();
	
        for _ in 0..visible_creature_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let creature_id = parse_input!(inputs[0], i32);
            let creature_x = parse_input!(inputs[1], i32);
            let creature_y = parse_input!(inputs[2], i32);
            let creature_vx = parse_input!(inputs[3], i32);
            let creature_vy = parse_input!(inputs[4], i32);
	    visible_fishes.push(Fish {fish_id:creature_id,pos: Point{x:creature_x, y:creature_y},pos_prev:None,speed: Point{x:creature_vx, y:creature_vy}, detail: *hash_fish.get(&creature_id).unwrap()});
        }

        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let radar_blip_count = parse_input!(input_line, i32);
        for _ in 0..radar_blip_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let creature_id = parse_input!(inputs[1], i32);
            let radar = inputs[2].trim(); //.to_string();

	    let radar_dir = match radar {
		"BL" => Ok(RadarDir::BL),
		"TL" => Ok(RadarDir::TL),
		"TR" => Ok(RadarDir::TR),
		"BR" => Ok(RadarDir::BR),
		_ => Err("Bad radar direction"),
	    };

	    	    
	    my_drones.iter_mut()
		.find(|e| e.drone_id == drone_id)
		.unwrap()
		.radars.as_mut().unwrap().push(RadarBlip {fish_id:creature_id, dir:radar_dir.unwrap(),fish_detail: *hash_fish.get(&creature_id).unwrap()});
        }
	
	let input_board = InputlBoard {fish_details:hash_fish.clone(), my_scans, opp_scans, my_drones, opp_drones, my_score:my_score, opp_score:foe_score, visible_fishes};
	let board = Board::from_input_board(&input_board).next_board(&vec![]);
	
	//let g_a = GridApprox::from_board(&board);
	//eprintln!("{:?}", g_a);
	let start = Instant::now();

	for (idx, d) in board.my_drones.iter().enumerate() {


	    
	    let mut light = false;
	    
	    
	    let tmp = board.dfs(d.pos, Point {x:d.pos.x, y:500});
	    let mut target  = Point {x:d.pos.x, y:500};
	    if let Some(dest) = tmp {
		target = dest[1];
		 eprintln!("PATH first {:?}", dest);
	    }
	   
	    
	    

	    
	    if d.scans.len() < 5 {
		let loc = d.where_i_am();
		if d.battery >= 5 && loc != MapLocation::T && (cur_step + idx) % 3 == 0 {
                    light = true;
		}
		
		for rb in d.radars.as_ref().unwrap() {
		    if rb.fish_detail.fish_type == -1 {
			continue; //we don't want monster...
		    }
		    if let Some(_) = board.my_scans.iter().find(|e| e == &&rb.fish_id) {
			continue;
		    }
		    if let Some(_) = d.scans.iter().find(|e| e == &&rb.fish_id) {
			continue;
		    }

		    let tmp = board.dfs(d.pos, board.grid_sliced[rb.fish_id as usize].unwrap().center());
		    //eprintln!("target {}", board.grid_sliced[rb.fish_id as usize].unwrap().center());
		    //eprintln!("PATH {:?}", tmp);
		    //eprintln!("FP");
		    
		    if let Some(t) = tmp {
			target = t[1];
		    }
		    else {
			eprintln!("Not found !!");
			eprintln!("target {}", board.grid_sliced[rb.fish_id as usize].unwrap().center());
		    }
		    //target = go_dir(&rb.dir);
		}

	    }
	    //light = false;
	    let ac = Action::MOVE(target, light);
	    println!("{}", ac);
	    prev_action[d.drone_id as usize] = Some(ac);
	}
	let duration = start.elapsed();
	eprintln!("TIME {:?}", duration);
	cur_step += 1;
    }
}
