# length(geoind)
# geoind[13:20]
# geoind[18]
# #R Function to get the latitude and longitude of a street address
# function(geo){
#   url = paste('http://maps.google.com/maps/api/geocode/xml?address=', addr,
#               '&sensor=false&key=AIzaSyDXF1umP-MpC_gF5SV6RMQaSWxcsktfXx4',sep='')  # construct the URL
#   doc = xmlTreeParse(url)
#   root = xmlRoot(doc)
#   lat = xmlValue(root[['result']][['geometry']][['location']][['lat']])
#   lon = xmlValue(root[['result']][['geometry']][['location']][['lng']])
#   return(paste(addr, c(lat, lon)))
# }

# detdem$site_location_detdemlatlon[which(is.na(laqtlon))] <- sapply(geoind, geo) # Non funziona..


# # CODE TO GET THE LATITUDE AND LONGITUDE OF A STREET ADDRESS WITH GOOGLE API
# addr <- '15860 W GRAND RIVER, DETROIT, US'  # set your address here
# url = paste('http://maps.google.com/maps/api/geocode/xml?address=', addr,'&sensor=false',sep='')  # construct the URL
# doc = xmlTreeParse(url) 
# root = xmlRoot(doc) 
# lat = xmlValue(root[['result']][['geometry']][['location']][['lat']]) 
# lon = xmlValue(root[['result']][['geometry']][['location']][['lng']]) 
# #lat
# #[1] "12.9725020"
# #lo
# #[1] "77.6510688"


# setwd("~/MEGA/Git Repository/Capstone - datasci_course_materials/capstone")
setwd("E:/MEGA/Git Repository/Capstone - datasci_course_materials/capstone")

# Enable JIT function compilation 
require(compiler)
enableJIT(3)


set.seed(329)
options(digits=11)
options(warn=1)
Sys.setlocale("LC_TIME", "English")

options(jupyter.plot_mimetypes = 'image/png')
library(stringr)
library(ggmap)
library("RJSONIO")
library("magrittr")
library(png)
library(gridExtra)
library(dbscan)
library(png)
library(grid)
library(ggplot2)
library(ggmap)
library(igraph)
library(leaderCluster)
library(alphahull)
library(sp)
library(plyr) # for reordering lat lon plygon
library(RColorBrewer)
library(caret)
library(e1071)
library(arm)


# #########################################################################
#                                                                         # 
# ahull function (ashape package) has to be fixed because the error:      #
# 'object 'case' not found.                                               #
# #########################################################################

ahull <- function (x, y = NULL, alpha) 
{
        ashape.obj <- ashape(x, y, alpha)
        compl <- complement(ashape.obj$delvor.obj, alpha = alpha)
        pm.x <- (compl[, "x1"] + compl[, "x2"]) * 0.5
        pm.y <- (compl[, "y1"] + compl[, "y2"]) * 0.5
        dm <- sqrt((compl[, "x1"] - compl[, "x2"])^2 + (compl[, "y1"] - 
                                                                compl[, "y2"])^2) * 0.5
        ashape.edges <- matrix(ashape.obj$edges[, c("ind1", "ind2")], 
                               ncol = 2, byrow = FALSE)
        noforget <- ashape.obj$alpha.extremes
        ind2 <- integer()
        j <- 0
        case <- 0  # Gianfranco Campana bugfixed
        nshape <- length(ashape.edges) * 0.5
        arcs <- matrix(0, nrow = nshape, ncol = 6)
        indp <- matrix(0, nrow = nshape, ncol = 2)
        cutp <- ashape.obj$x
        if (nshape > 0) {
                for (i in 1:nshape) {
                        ind <- which(ashape.edges[i, 1] == compl[, "ind1"] & 
                                             ashape.edges[i, 2] == compl[, "ind2"])
                        if (length(ind) > 0) {
                                if (!((1 <= sum((compl[ind, "ind"] == 1))) & 
                                      (sum((compl[ind, "ind"] == 1)) < length(ind)))) {
                                        which <- which(compl[ind, "r"] == min(compl[ind[compl[ind, 
                                                                                              "r"] > 0], "r"]))
                                        j <- j + 1
                                        arcs[j, ] <- c(compl[ind[which], 1], compl[ind[which], 
                                                                                   2], compl[ind[which], 3], compl[ind[which], 
                                                                                                                   "v.x"], compl[ind[which], "v.y"], compl[ind[which], 
                                                                                                                                                           "theta"])
                                        vaux <- compl[ind[which], c("x1", "y1")] - 
                                                cbind(pm.x, pm.y)[ind[which], ]
                                        theta.aux <- rotation(compl[ind[which], c("v.x", 
                                                                                  "v.y")], compl[ind[which], "theta"])
                                        a2 <- sum(vaux * theta.aux)
                                        if (a2 > 0) {
                                                indp[j, ] <- compl[ind[which], c("ind1", 
                                                                                 "ind2")]
                                        }
                                        else {
                                                indp[j, ] <- compl[ind[which], c("ind2", 
                                                                                 "ind1")]
                                        }
                                }
                                ind2 <- c(ind2, ind)
                        }
                }
        }
        arcs.old <- arcs[arcs[, 3] > 0, ]
        colnames(arcs.old) <- c("c1", "c2", "r", "v.x", "v.y", "theta")
        arcs <- arcs.old
        indp <- indp[indp[, 1] != 0 & indp[, 2] != 0, ]
        n.arc <- dim(arcs)[1]
        watch <- 1
        j <- 1
        if (n.arc > 0) {
                while (watch <= n.arc) {
                        ind.arc <- 1:n.arc
                        while (j <= n.arc) {
                                if (j != watch) {
                                        intersection <- inter(arcs[watch, 1], arcs[watch, 
                                                                                   2], arcs[watch, 3], arcs[j, 1], arcs[j, 2], 
                                                              arcs[j, 3])
                                        if (intersection$n.cut == 2) {
                                                v.arc <- c(arcs[watch, "v.x"], arcs[watch, 
                                                                                    "v.y"])
                                                if (v.arc[2] >= 0) {
                                                        ang.OX <- acos(v.arc[1])
                                                }
                                                else {
                                                        ang.OX <- 2 * pi - acos(v.arc[1])
                                                }
                                                v.arc.rot <- rotation(v.arc, ang.OX)
                                                v.int <- intersection$v1
                                                v.int.rot <- rotation(v.int, ang.OX)
                                                if (v.int.rot[2] >= 0) {
                                                        ang.v.int.rot.OX <- acos(v.int.rot[1])
                                                        angles <- c(-arcs[watch, "theta"], arcs[watch, 
                                                                                                "theta"], ang.v.int.rot.OX - intersection$theta1, 
                                                                    ang.v.int.rot.OX + intersection$theta1)
                                                        names(angles) <- c("theta1", "theta2", 
                                                                           "beta1", "beta2")
                                                        order <- names(sort(angles))
                                                        theta1 <- ang.OX - arcs[watch, "theta"]
                                                        theta2 <- ang.OX + arcs[watch, "theta"]
                                                        beta1 <- ang.v.int.rot.OX + ang.OX - intersection$theta1
                                                        beta2 <- ang.v.int.rot.OX + ang.OX + intersection$theta1
                                                }
                                                else {
                                                        ang.v.int.rot.OX <- acos(v.int.rot[1])
                                                        angles <- c(-arcs[watch, "theta"], arcs[watch, 
                                                                                                "theta"], -ang.v.int.rot.OX - intersection$theta1, 
                                                                    -ang.v.int.rot.OX + intersection$theta1)
                                                        names(angles) <- c("theta1", "theta2", 
                                                                           "beta1", "beta2")
                                                        order <- names(sort(angles))
                                                        theta1 <- ang.OX - arcs[watch, "theta"]
                                                        theta2 <- ang.OX + arcs[watch, "theta"]
                                                        beta1 <- -ang.v.int.rot.OX + ang.OX - intersection$theta1
                                                        beta2 <- -ang.v.int.rot.OX + ang.OX + intersection$theta1
                                                }
                                                if (sum(match(indp[watch, ], indp[j, ], nomatch = 0)) > 
                                                    0) {
                                                        coinc <- indp[j, sum(match(indp[watch, 
                                                                                        ], indp[j, ], nomatch = 0))]
                                                        if (indp[watch, 1] == indp[j, 2]) {
                                                                if (all(order == c("beta1", "beta2", 
                                                                                   "theta1", "theta2"))) {
                                                                        case <- 1
                                                                }
                                                                else if (all(order == c("theta1", "beta1", 
                                                                                        "beta2", "theta2"))) {
                                                                        case <- 2
                                                                }
                                                                else if (all(order == c("beta1", "theta1", 
                                                                                        "beta2", "theta2"))) {
                                                                        ang.control <- (angles["theta1"] - 
                                                                                                angles["beta1"])/2
                                                                        if (abs(ang.control) < 1e-05) {
                                                                                case <- 2
                                                                        }
                                                                        else {
                                                                                case <- 1
                                                                        }
                                                                }
                                                                if (case == 2) {
                                                                        ang.middle2 <- (angles["theta2"] - 
                                                                                                angles["beta2"])/2
                                                                        v.new2 <- rotation(c(1, 0), -arcs[watch, 
                                                                                                          "theta"] + ang.middle2 - ang.OX)
                                                                        cutp <- rbind(cutp, arcs[watch, 1:2] + 
                                                                                              arcs[watch, 3] * rotation(v.new2, 
                                                                                                                        ang.middle2))
                                                                        inn <- dim(cutp)[1]
                                                                        arcs[watch, 4:6] <- c(v.new2, ang.middle2)
                                                                        indp[watch, 1] <- inn
                                                                        pmaux <- (cutp[inn, ] + cutp[indp[j, 
                                                                                                          1], ]) * 0.5
                                                                        dmaux <- pmaux - cutp[indp[j, 1], ]
                                                                        ndmaux <- sqrt(sum(dmaux^2))
                                                                        vaux <- pmaux - arcs[j, 1:2]
                                                                        nvaux <- sqrt(sum(vaux^2))
                                                                        th <- atan(ndmaux/nvaux)
                                                                        arcs[j, 4:6] <- c(vaux/nvaux, th)
                                                                        indp[j, 2] <- inn
                                                                }
                                                        }
                                                        else if (indp[watch, 2] == indp[j, 1]) {
                                                                if (all(order == c("theta1", "theta2", 
                                                                                   "beta1", "beta2"))) {
                                                                        case <- 1
                                                                }
                                                                else if (all(order == c("theta1", "beta1", 
                                                                                        "beta2", "theta2"))) {
                                                                        case <- 2
                                                                }
                                                                else if (all(order == c("theta1", "beta1", 
                                                                                        "theta2", "beta2"))) {
                                                                        ang.control <- (angles["theta2"] - 
                                                                                                angles["beta2"])/2
                                                                        if (abs(ang.control) < 1e-05) {
                                                                                case <- 2
                                                                        }
                                                                        else {
                                                                                case <- 1
                                                                        }
                                                                }
                                                                if (case == 2) {
                                                                        ang.middle <- (angles["beta1"] - angles["theta1"])/2
                                                                        v.new <- rotation(c(1, 0), arcs[watch, 
                                                                                                        "theta"] - ang.middle - ang.OX)
                                                                        cutp <- rbind(cutp, arcs[watch, 1:2] + 
                                                                                              arcs[watch, 3] * rotation(v.new, 
                                                                                                                        -ang.middle))
                                                                        inn <- dim(cutp)[1]
                                                                        arcs[watch, 4:6] <- c(v.new, ang.middle)
                                                                        indp[watch, 2] <- inn
                                                                        pmaux <- (cutp[inn, ] + cutp[indp[j, 
                                                                                                          2], ]) * 0.5
                                                                        dmaux <- pmaux - cutp[indp[j, 2], ]
                                                                        ndmaux <- sqrt(sum(dmaux^2))
                                                                        vaux <- pmaux - arcs[j, 1:2]
                                                                        nvaux <- sqrt(sum(vaux^2))
                                                                        th <- atan(ndmaux/nvaux)
                                                                        arcs[j, 4:6] <- c(vaux/nvaux, th)
                                                                        indp[j, 1] <- inn
                                                                }
                                                        }
                                                }
                                                else if (all(order == c("theta1", "beta1", 
                                                                        "beta2", "theta2"))) {
                                                        v.arcj <- c(arcs[j, "v.x"], arcs[j, "v.y"])
                                                        if (v.arcj[2] >= 0) {
                                                                ang.OXj <- acos(v.arcj[1])
                                                        }
                                                        else {
                                                                ang.OXj <- 2 * pi - acos(v.arcj[1])
                                                        }
                                                        v.arc.rotj <- rotation(v.arcj, ang.OXj)
                                                        v.intj <- intersection$v2
                                                        v.int.rotj <- rotation(v.intj, ang.OXj)
                                                        if (v.int.rotj[2] >= 0) {
                                                                ang.v.int.rot.OXj <- acos(v.int.rotj[1])
                                                                anglesj <- c(-arcs[j, "theta"], arcs[j, 
                                                                                                     "theta"], ang.v.int.rot.OXj - intersection$theta2, 
                                                                             ang.v.int.rot.OXj + intersection$theta2)
                                                                names(anglesj) <- c("theta1", "theta2", 
                                                                                    "beta1", "beta2")
                                                                orderj <- names(sort(anglesj))
                                                                theta1j <- ang.OXj - arcs[j, "theta"]
                                                                theta2j <- ang.OXj + arcs[j, "theta"]
                                                                beta1j <- ang.v.int.rot.OXj + ang.OXj - 
                                                                        intersection$theta2
                                                                beta2j <- ang.v.int.rot.OXj + ang.OXj + 
                                                                        intersection$theta2
                                                        }
                                                        else {
                                                                ang.v.int.rot.OXj <- acos(v.int.rotj[1])
                                                                anglesj <- c(-arcs[j, "theta"], arcs[j, 
                                                                                                     "theta"], -ang.v.int.rot.OXj - intersection$theta2, 
                                                                             -ang.v.int.rot.OXj + intersection$theta2)
                                                                names(anglesj) <- c("theta1", "theta2", 
                                                                                    "beta1", "beta2")
                                                                orderj <- names(sort(anglesj))
                                                                theta1j <- ang.OXj - arcs[j, "theta"]
                                                                theta2j <- ang.OXj + arcs[j, "theta"]
                                                                beta1j <- -ang.v.int.rot.OXj + ang.OXj - 
                                                                        intersection$theta2
                                                                beta2j <- -ang.v.int.rot.OXj + ang.OXj + 
                                                                        intersection$theta2
                                                        }
                                                        if (all(orderj == c("theta1", "beta1", 
                                                                            "beta2", "theta2"))) {
                                                                ang.middle <- (angles["beta1"] - angles["theta1"])/2
                                                                v.new <- rotation(c(1, 0), arcs[watch, 
                                                                                                "theta"] - ang.middle - ang.OX)
                                                                ang.middle2 <- (angles["theta2"] - angles["beta2"])/2
                                                                v.new2 <- rotation(c(1, 0), -arcs[watch, 
                                                                                                  "theta"] + ang.middle2 - ang.OX)
                                                                arcs <- rbind(arcs, c(arcs[watch, 1], 
                                                                                      arcs[watch, 2], arcs[watch, 3], v.new2[1], 
                                                                                      v.new2[2], ang.middle2))
                                                                arcs[watch, ] <- c(arcs[watch, 1], arcs[watch, 
                                                                                                        2], arcs[watch, 3], v.new[1], v.new[2], 
                                                                                   ang.middle)
                                                                n.arc <- n.arc + 1
                                                                np1 <- arcs[watch, 1:2] + arcs[watch, 
                                                                                               3] * rotation(v.new, -ang.middle)
                                                                np2 <- arcs[watch, 1:2] + arcs[watch, 
                                                                                               3] * rotation(v.new2, ang.middle2)
                                                                indold <- indp[watch, 2]
                                                                inn1 <- dim(cutp)[1] + 1
                                                                inn2 <- dim(cutp)[1] + 2
                                                                indp[watch, 2] <- inn1
                                                                indp <- rbind(indp, c(inn2, indold))
                                                                cutp <- rbind(cutp, np1)
                                                                cutp <- rbind(cutp, np2)
                                                                indold <- indp[j, 1]
                                                                indp[j, 1] <- inn1
                                                                indp <- rbind(indp, c(indold, inn2))
                                                                pmaux <- (cutp[inn1, ] + cutp[indp[j, 
                                                                                                   2], ]) * 0.5
                                                                dmaux <- pmaux - cutp[indp[j, 2], ]
                                                                ndmaux <- sqrt(sum(dmaux^2))
                                                                vaux <- pmaux - arcs[j, 1:2]
                                                                nvaux <- sqrt(sum(vaux^2))
                                                                th <- atan(ndmaux/nvaux)
                                                                arcs[j, 4:6] <- c(vaux/nvaux, th)
                                                                pmaux <- (cutp[inn2, ] + cutp[indold, 
                                                                                              ]) * 0.5
                                                                dmaux <- pmaux - cutp[indold, ]
                                                                ndmaux <- sqrt(sum(dmaux^2))
                                                                vaux <- pmaux - arcs[j, 1:2]
                                                                nvaux <- sqrt(sum(vaux^2))
                                                                th <- atan(ndmaux/nvaux)
                                                                arcs <- rbind(arcs, c(arcs[j, 1:3], vaux/nvaux, 
                                                                                      th))
                                                                n.arc <- n.arc + 1
                                                        }
                                                }
                                        }
                                        case <- 0
                                }
                                j <- j + 1
                        }
                        watch <- watch + 1
                        j <- 1
                }
                ord.old <- 1:dim(indp)[1]
                ord.new <- numeric()
                while (length(ord.new) < length(ord.old)) {
                        if (length(ord.new) == 0) {
                                ord.new <- 1
                        }
                        else {
                                ord.new <- c(ord.new, ord.old[-ord.new][1])
                        }
                        coinc <- match(indp[ord.new[length(ord.new)], 2], 
                                       indp[-ord.new, 1])
                        while (!is.na(coinc)) {
                                ord.new <- c(ord.new, ord.old[-ord.new][coinc])
                                coinc <- match(indp[ord.new[length(ord.new)], 
                                                    2], indp[-ord.new, 1])
                        }
                }
                indp <- indp[ord.new, ]
                ahull.arcs <- cbind(arcs[ord.new, ], indp)
                colnames(ahull.arcs) <- c("c1", "c2", "r", "v.x", "v.y", 
                                          "theta", "end1", "end2")
                lengthah <- lengthahull(arcs)
                addp <- noforget[is.na(match(noforget, indp))]
                num <- length(addp)
                if (num > 0) {
                        mat.noforget <- cbind(matrix(ashape.obj$x[addp, 1:2], 
                                                     ncol = 2, byrow = FALSE), rep(0, num), rep(0, 
                                                                                                num), rep(0, num), rep(0, num), addp, addp)
                        ahull.arcs <- rbind(ahull.arcs, mat.noforget)
                }
        }
        else {
                num <- length(noforget)
                ahull.arcs <- cbind(ashape.obj$x[noforget, ], rep(0, 
                                                                  num), rep(0, num), rep(0, num), rep(0, num), noforget, 
                                    noforget)
                colnames(ahull.arcs) <- c("c1", "c2", "r", "v.x", "v.y", 
                                          "theta", "end1", "end2")
                lengthah <- 0
        }
        ahull.obj <- list(arcs = ahull.arcs, xahull = cutp, length = lengthah, 
                          complement = compl, alpha = alpha, ashape.obj = ashape.obj)
        class(ahull.obj) <- "ahull"
        invisible(ahull.obj)
}

# #########################################################################
#                                                                         # 
# Define a function that will process geocode from Google                 #
#                                                                         #
# #########################################################################
getGeoDetails <- function(address){   
  #use the gecode function to query google servers
  geo_reply = geocode(address, output='all', messaging=TRUE, override_limit=TRUE)
  #now extract the bits that we need from the returned list
  answer <- data.frame(lat=NA, long=NA, accuracy=NA, formatted_address=NA, address_type=NA, status=NA)
  answer$status <- geo_reply$status
  
  #if we are over the query limit - want to pause for an hour
  while(geo_reply$status == "OVER_QUERY_LIMIT"){
    print("OVER QUERY LIMIT - Pausing for 1 hour at:") 
    time <- Sys.time()
    print(as.character(time))
    Sys.sleep(60*60)
    geo_reply = geocode(address, output='all', messaging=TRUE, override_limit=TRUE)
    answer$status <- geo_reply$status
  }
  
  #return Na's if we didn't get a match:
  if (geo_reply$status != "OK"){
    return(answer)
  }   
  #else, extract what we need from the Google server reply into a dataframe:
  answer$lat  <- geo_reply$results[[1]]$geometry$location$lat
  answer$long <- geo_reply$results[[1]]$geometry$location$lng   
  if (length(geo_reply$results[[1]]$types) > 0){
    answer$accuracy <- geo_reply$results[[1]]$types[[1]]
  }
  answer$address_type      <- paste(geo_reply$results[[1]]$types, collapse=',')
  answer$formatted_address <- geo_reply$results[[1]]$formatted_address
  
  return(answer)
}
# #########################################################################
#                                                                         # 
# Define the multiplot function                                           #
#                                                                         #
# #########################################################################

# ggplot objects can be passed in ..., or to plotlist (as a list of ggplot objects)
# - cols:   Number of columns in layout
# - layout: A matrix specifying the layout. If present, 'cols' is ignored.
#
# If the layout is something like matrix(c(1,2,3,3), nrow=2, byrow=TRUE),
# then plot 1 will go in the upper left, 2 will go in the upper right, and
# 3 will go all the way across the bottom.
#
# multiplot <- function(..., plotlist=NULL, file, cols=1, layout=NULL) {
#   library(grid)
#   
#   # Make a list from the ... arguments and plotlist
#   plots <- c(list(...), plotlist)
#   
#   numPlots = length(plots)
#   
#   # If layout is NULL, then use 'cols' to determine layout
#   if (is.null(layout)) {
#     # Make the panel
#     # ncol: Number of columns of plots
#     # nrow: Number of rows needed, calculated from # of cols
#     layout <- matrix(seq(1, cols * ceiling(numPlots/cols)),
#                      ncol = cols, nrow = ceiling(numPlots/cols))
#   }
#   
#   if (numPlots==1) {
#     print(plots[[1]])
#     
#   } else {
#     # Set up the page
#     grid.newpage()
#     pushViewport(viewport(layout = grid.layout(nrow(layout), ncol(layout))))
#     
#     # Make each plot, in the correct location
#     for (i in 1:numPlots) {
#       # Get the i,j matrix positions of the regions that contain this subplot
#       matchidx <- as.data.frame(which(layout == i, arr.ind = TRUE))
#       
#       print(plots[[i]], vp = viewport(layout.pos.row = matchidx$row,
#                                       layout.pos.col = matchidx$col))
#     }
#   }
# }
# 

#'Plot multiple plots in a single pane
#'
#'ggplot objects can be passed in ..., or to plotlist (as a list of ggplot objects)
#' @import grid ggplot2
#' @export
#' 
#' @param ... Two or more ggplot2 objects
#' @param  plotlist (optional) a list of ggplot2 objects
#' @param  cols Number of columns in layout
#' @param  layout A matrix specifying the layout. If present, 'cols' is ignored. See Details
#' @param  title Optional title as a character string
#' @param  widths a vector of relative column widths eg. c(3,2)
#' @param  heights a vector of relative column heights eg. c(3,2)
#' @param  titlefont The font of the title
#' @param  titleface The font face (1 = normal, 2 = bold, 3 = italic, 4 = bold italic)
#' @param  titlesize The size of the title font
#' 
#' @details If plotting three plots and the layout is something like
#'   matrix(c(1,2,3,3), nrow=2, byrow=TRUE), then plot 1 will go in the upper
#'   left, 2 will go in the upper right, and 3 will go all the way across the
#'   bottom.  To save, you must use the desired device (eg \code{png()}), or
#'   save from the RStudio Viewer.
#' 
#' Borrowed and modified from http://www.cookbook-r.com/Graphs/Multiple_graphs_on_one_page_(ggplot2)/
#' 
#' @return NULL (invisibly)
#' @examples \dontrun{
#' library("ggplot2")
#' plot1 <- ggplot(iris, aes(x = Species, y = Sepal.Length)) + 
#'    geom_bar(stat = "identity")
#' plot2 <- ggplot(mtcars, aes(x = mpg, y = disp)) + 
#'    geom_smooth()
#' multiplot(plot1, plot2, cols = 2, widths = c(3,2), title = "My two unrelated plots")
#' multiplot(plot1, plot2, cols = 1, heights = c(10,2), title = "My two unrelated plots")
#' myplots <- list(plot1, plot2, plot1)
#' multiplot(plotlist = myplots, layout =matrix(c(1,2,3,3), nrow=2), 
#'      heights = c(1,3), widths = c(3,4), title = "My three unrelated plots")
#' ## Adjusting fonts
#' library(extrafont)
#' loadfonts()
#' multiplot(plotlist = myplots, layout =matrix(c(1,2,3,3), nrow=2),
#'           heights = c(1,3), widths = c(3,4), title = "My three unrelated plots", 
#'           titlefont = "Wingdings", titleface = 4, titlesize = 20)
#'}
multiplot <- function(..., plotlist=NULL, cols=1, layout=NULL, widths=NULL, heights=NULL, 
                      title=NULL, titlefont = "", titleface = 1, titlesize = 16) {
        
        # Make a list from the ... arguments and plotlist
        plots <- c(list(...), plotlist)
        
        numPlots = length(plots)
        
        # If layout is NULL, then use 'cols' to determine layout
        if (is.null(layout)) {
                # Make the panel
                # ncol: Number of columns of plots
                # nrow: Number of rows needed, calculated from # of cols
                layout <- matrix(seq(1, cols * ceiling(numPlots/cols)),
                                 ncol = cols, nrow = ceiling(numPlots/cols))
        }
        
        if (!is.null(title)) { # Add a narrow row at the top for the title
                layout <- rbind(rep(0,ncol(layout)),layout)
                if (is.null(heights)) {
                        plotrows <- nrow(layout)-1
                        rowheights <- c(0.1, rep(1,plotrows)/plotrows)
                } else {
                        rowheights <- c(0.1, heights/sum(heights))
                }
        } else {
                if (is.null(heights)) {
                        rowheights <- rep(1,nrow(layout))  
                } else {
                        rowheights <- heights
                }
        }
        
        if (is.null(widths)) {
                colwidths <- rep(1, cols)
        } else {
                colwidths <- widths
        }
        
        if (numPlots==1) {
                
                return(plots[[1]] + labs(title=title))
                
        } else {
                # Set up the page
                grid.newpage()
                pushViewport(viewport(layout = grid.layout(nrow(layout), ncol(layout), 
                                                           widths=colwidths, 
                                                           heights=rowheights)))
                
                # Make each plot, in the correct location
                for (i in 1:numPlots) {
                        # Get the i,j matrix positions of the regions that contain this subplot
                        matchidx <- as.data.frame(which(layout == i, arr.ind = TRUE))
                        
                        print(plots[[i]], vp = viewport(layout.pos.row = matchidx$row,
                                                        layout.pos.col = matchidx$col))
                }
                
                if (!is.null(title)) {
                        grid.text(title, vp = viewport(layout.pos.row = 1
                                                       , layout.pos.col = 1:ncol(layout)), 
                                  gp = gpar(fontfamily = titlefont, fontface = titleface, 
                                            fontsize = titlesize))
                }
                
        }
        return(invisible(NULL))
}


# #########################################################################
#                                                                         # 
# Define a function to create style string fro Gmap                       #
#                                                                         #
# #########################################################################
create_style_string <- function(style_list){
  style_string <- ""
  for(i in 1:length(style_list)){
    if("featureType" %in% names(style_list[[i]])){
      style_string <- paste0(style_string, "feature:", 
                             style_list[[i]]$featureType, "|")      
    }
    elements <- style_list[[i]]$stylers
    a <- lapply(elements, function(x)paste0(names(x), ":", x)) %>%
      unlist() %>%
      paste0(collapse="|")
    style_string <- paste0(style_string, a)
    if(i < length(style_list)){
      style_string <- paste0(style_string, "&style=")       
    }
  }  
  # google wants 0xff0000 not #ff0000
  style_string <- gsub("#", "0x", style_string)
  return(style_string)
  
}


# #########################################################################
#                                                                         # 
# Define a function to save a Google Map for every poi                    #
#                                                                         #
# #########################################################################
# savemap <- function(poi) {
#   style <- paste0('[
#                   {
#                   "stylers": [
#                   { "saturation": -100 },
#                   { "lightness": 40 }
#                   ]
#                   },{
#                   "featureType": "poi.', poi, '",
#                   "elementType": "geometry.fill",
#                   "stylers": [
#                   { "color": "#ff0000" },
#                   { "gamma": 0.5 }
#                   ]
#                   }
#                   ]')
#   style_list <- fromJSON(style, asText=TRUE)
#   map_style  <- create_style_string(style_list)
#   
#   p <- ggmap(get_googlemap("42.330358, -83.086847", zoom=11, style=map_style), extent="device")
#   print(p)
#   ggsave(p, filename=paste0("./blight/data/map_", poi, "_zoom11.png"))
# }


savemappoi <- function(poilist, dataframe) {
        lcplots <- list()
        for (currentpoi in poilist) {
                style <- paste0('[
                                {
                                "stylers": [
                                { "saturation": -100 },
                                { "lightness": 40 }
                                ]
                                },{
                                "featureType": "poi.', currentpoi, '",
                                "elementType": "geometry.fill",
                                "stylers": [
                                { "color": "#ff0000" },
                                { "gamma": 0.5 }
                                ]
                                },{
                                "featureType": "water",
                                "elementType": "geometry.fill",
                                "stylers": [
                                { "color": "#0000ff" }
                                ]
                                }
                                ]')
                style_list <- fromJSON(style, asText=TRUE)
                map_style  <- create_style_string(style_list)
                p <- ggmap(get_googlemap("42.330358, -83.086847", zoom=11, style=map_style, alpha=.5), extent="device") +
                        theme_bw() +
                        theme(
                                plot.background = element_blank()
                                ,panel.grid.major = element_blank()
                                ,panel.grid.minor = element_blank()
                                ,panel.border = element_blank()
                                ,legend.position = "none") +
                        # geom_point(alpha = .5, aes(
                        #         scale_fill = "white",
                        #         size = 1,
                        #         stroke = 1), shape = 21, fill = "white", lc_centroids)  +
                        # geom_point(data=lc_centroids)  +
                        # geom_label(data=lc_centroids, aes(x = lon, y = lat, label = as.character(cluster_id)))  +
                        stat_bin2d(
                                aes(x = lon, y = lat, colour = as.factor(cluster_id), fill = as.factor(cluster_id), drop = T),
                                size = .5, bins = 52, alpha = 0.3,
                                data = dataframe
                        ) +
                        # geom_line(data=coords, aes(x=lon, y=lat)) +
                        ggtitle(paste0(toupper(currentpoi))) + 
                        theme(plot.margin=unit(c(5,5,5.5,5.2),"points"))
                
                # print(p)
                # ggsave(p, filename=paste0("./blight/data/map_", currentpoi, "_zoom11.png"))
                lcplots[[paste0("map_", currentpoi)]] <- p
        }
        
        multiplot(plotlist = lcplots, cols=2, title = "Demolition Permits by Point of Interest (in red)\n clustered on lat/lon (haversine)", titlesize = 14, titleface = 3)
        dev.copy2pdf(file = "./blight/data/demolition_by_poi_haversine_latlon.pdf", width = 28, height = 28)
        # dev.copy(png, file = "./blight/data/demolition_by_poi_haversine_latlon.png", width = 28, height = 28)
        }

# savemappoi(poi, detdem)





# x <- list(a=11,b=12,c=13) # Changed to list to address concerns in commments
# lapply(seq_along(x), function(y, n, i) { paste(n[[i]], y[[i]]) }, y=x, n=names(x))

# Here I use lapply over the indices of x, but also pass in x and the names of x. As you can see, the order of the 
# function arguments can be anything - lapply will pass in the "element" (here the index) to the first argument 
# not specified among the extra ones. In this case, I specify y and n, so there's only i left...

# savemapchull <- function(dflist) {
#         style <- paste0('[
#                         {
#                         "stylers": [
#                         { "saturation": -100 },
#                         { "lightness": 40 }
#                         ]
#                         },{
#                         "featureType": "water",
#                         "elementType": "geometry.fill",
#                         "stylers": [
#                         { "color": "#0000ff" }
#                         ]
#                         }
#                         ]')
#         style_list <- fromJSON(style, asText=TRUE)
#         map_style  <- create_style_string(style_list)
#         
#         p <- ggmap(get_googlemap("42.330358, -83.086847", zoom=11, style=map_style, alpha=.5), extent="device") + 
#                 theme_bw() +
#                 theme(
#                         plot.background = element_blank()
#                         ,panel.grid.major = element_blank()
#                         ,panel.grid.minor = element_blank()
#                         ,panel.border = element_blank()
#                         ,legend.position = "none") +
#                 ggtitle(paste0(toupper("Buildings by convex hull of clusters"))) + 
#                 theme(plot.margin=unit(c(5,5,5.5,5.2),"points"))
#         print(p)
#         for (i in names(dflist)) {
#                 # lapply(seq_along(dflist), function(i, chdf, nameschdf) {           
#                 # print(paste("ecco p: ", p)
#                 p <- p + 
#                         geom_polygon(data=dflist[[i]], aes(x=lon, y=lat), alpha=.4, fill=as.numeric(gsub("^ch", "", i)) ) +
#                         geom_label(data=lc_centroids, aes(x = lon, y = lat, label = as.character(cluster_id)))  
#                 print(p)
#                 # ggsave(p, filename=paste0("./blight/data/map_", currentpoi, "_zoom11.png"))
#         }
#         print(p)
#         dev.copy2pdf(file = "./blight/data/Buildings by convex hull of clusters.pdf", width = 28, height = 28)
# }
# savemapchull(ch)


# Plotting the alpha shape polygon

savemapashape <- function(dflist) {
    style <- paste0('[
                    {
                    "stylers": [
                    { "saturation": -100 },
                    { "lightness": 40 }
                    ]
                    },{
                    "featureType": "water",
                    "elementType": "geometry.fill",
                    "stylers": [
                    { "color": "#0000ff" }
                    ]
                    }
                    ]')
    style_list <- fromJSON(style, asText=TRUE)
    map_style  <- create_style_string(style_list)
    
    p <- ggmap(get_googlemap("42.330358, -83.086847", zoom=11, style=map_style, alpha=.5), extent="device") + 
        theme_bw() +
        theme(
            plot.background = element_blank()
            ,panel.grid.major = element_blank()
            ,panel.grid.minor = element_blank()
            ,panel.border = element_blank()
            ,legend.position = "none") +
        ggtitle(paste0(("Alpha Shape of clusters with perimeter points"))) + 
        theme(plot.margin=unit(c(5,5,5.5,5.2),"points"))
    fillc <- colorRampPalette(brewer.pal(9, "Set1"))(length(ash))
    cb <- 1
    for (i in names(dflist)) {
        p <- p + 
            geom_polygon(data = ash[[i]], 
                         fill = fillc[cb], 
                         alpha = .4) +
            geom_point(data = ash[[i]], fill="red", alpha = .4, size = .2) 
        cb = cb +1
    }
    p1 <- p
    
    p <- ggmap(get_googlemap("42.330358, -83.086847", zoom=11, style=map_style, alpha=.5), extent="device") +
            theme_bw() +
            theme(
                    plot.background = element_blank()
                    ,panel.grid.major = element_blank()
                    ,panel.grid.minor = element_blank()
                    ,panel.border = element_blank()
                    ,legend.position = "none") +
            ggtitle(paste0(("Frequence of blights per building"))) +
            theme(plot.margin=unit(c(5,5,5.5,5.2),"points"))
    fillc <- colorRampPalette(brewer.pal(9, "Set1"))(length(ash))
            p <- p +
                geom_text(data=cluster_freq, size = 2, aes(x = lon, y = lat, label = as.character(freq), col = "red"))
    p2 <- p

    multiplot(p1, p2, cols=1, title = toupper("Buildings by Alpha Shape of clusters \n by haversine distance up to 300 meters"))
    dev.copy2pdf(file = "./blight/data/Buildings by Alpha Shape of clusters 300m.pdf", width = 22.275, height = 31.5)
}


# savemapashape(ash)




# #########################################################################
#                                                                         # 
# Test to apply analysis on live data                                     #
#                                                                         #
# #########################################################################
# library(jsonlite)
# rl <- "https://data.detroitmi.gov/resource/uzpg-2pfj.json"
# detdemlive <- fromJSON(txt=url)
# # url at socrata including token from personal Application account
# urldetdem <- "https://data.detroitmi.gov/resource/uzpg-2pfj.json?$$app_token=B3uSqwUCzxfm3z1xCCV4enURf"
# detdemlive <- fromJSON(txt=urldetdem)
# read url and convert to data.frame
# detdemlive$location <- NULL



# #########################################################################
#                                                                         # 
# Load datasets                                                           #
#                                                                         #
# #########################################################################
detviol  <- read.csv("./blight/data/detroit-blight-violations.csv", header = T, sep = ",", stringsAsFactors = F)   
det311   <- read.csv("./blight/data/detroit-311.csv", header = T, sep = ",", stringsAsFactors = F)     
detdem   <- read.csv("./blight/data/detroit-demolition-permits.tsv", header = T, sep="\t", stringsAsFactors = F)   
detcrime <- read.csv("./blight/data/detroit-crime.csv", header = T, sep=",", stringsAsFactors = F)     

names(detviol)  <- tolower(names(detviol))
names(det311)   <- tolower(names(det311))
names(detdem)   <- tolower(names(detdem))
names(detcrime) <- tolower(names(detcrime))

# library(googleVis)
# 
# gv <- unique(paste(as.character(pcf_amt_due), as.character(datevar)))
# 
# pcf_amt_due = as.numeric((gsub("\\$","",detdem$pcf_amt_due)))
# datevar = detdem$demdate
# AnnoTimeLine  <- gvisMotionChart(gv, idvar="pcf_amt_due", timevar="datevar", date.format = "%Y-%m-%d",
#                                        options=list(displayAnnotations=TRUE,
#                                                     legendPosition="newRow",
#                                                     width=600, height=300)
# )
# colnames(detdem)
# # Display chart
# plot(AnnoTimeLine) 
# # Create Google Gadget
# cat(createGoogleGadget(AnnoTimeLine), file="annotimeline.xml")
# 
# 
# 
# str(detdem$pcf_amt_due)
# str(as.numeric((gsub("\\$","",detdem$pcf_amt_due))))
# # as.numeric(format(MyDate, "%Y%m")) 
# table(as.numeric((gsub("\\$","",detdem$pcf_amt_due))))
# 
# 
# 
# dates <- seq(as.Date("2011/1/1"), as.Date("2011/12/31"), "days")
# happiness <- rnorm(365)^ 2
# happiness[333:365] <- happiness[333:365]  * 3 + 20
# Title <- NA
# Annotation <- NA
# df <- data.frame(dates, happiness, Title, Annotation)
# df$Title[333] <- "Discovers Google Viz"
# df$Annotation[333] <- "Google Viz API interface by Markus Gesmann causes acute increases in happiness."
# 
# ### Everything above here is just for making up data ### 
# ## from here down is the actual graphics bits        ###
# AnnoTimeLine  <- gvisAnnotatedTimeLine(df, datevar="dates",
#                                        numvar="happiness", 
#                                        titlevar="Title", annotationvar="Annotation",
#                                        options=list(displayAnnotations=TRUE,
#                                                     legendPosition='newRow',
#                                                     width=600, height=300)
# )
# # Display chart
# plot(AnnoTimeLine) 
# # Create Google Gadget
# cat(createGoogleGadget(AnnoTimeLine), file="annotimeline.xml")
# 
# 





# #########################################################################
#                                                                         # 
# Normalizet latitude and longitude from address in blight violation      #
#                                                                         #
# #########################################################################
detviollatlon <- strsplit(gsub("[\\)\\( ]", "", str_extract(detviol$violationaddress, "\\(.*\\)")), ",")
detviol$lat <- sapply(detviollatlon, "[[", 1)
detviol$lon <- sapply(detviollatlon, "[[", 2)
length(which(is.na(detviollatlon)))
detviol$lat <- as.numeric(detviol$lat)
detviol$lon <- as.numeric(detviol$lon)



# #########################################################################
#                                                                         # 
# Normalizet latitude and longitude from address in 311 calls             #
#                                                                         #
# #########################################################################
det311latlon <- strsplit(gsub("[\\)\\( ]", "", str_extract(det311$location, "\\(.*\\)")), ",")
det311$lat <- sapply(det311latlon, "[[", 1)
names(det311)[13] <- "lon"
det311$lon <- sapply(det311latlon, "[[", 2)
length(which(is.na(det311latlon)))
det311$lat <- as.numeric(det311$lat)
det311$lon <- as.numeric(det311$lon)  



# #########################################################################################
#                                                                                         # 
# Extract latitude and longitude for demolition_permits.                                  #
#       NOTE: 803 rows have no site_location at all. # which(detdem$site_location == "" ) #
#             14 rows have no lat/lon in site_location.                                   # 
#             Once normalized the address, perform the geocode.                           #
# #########################################################################################
# Normalize the site_location
detdem$site_location[which(detdem$site_location == "" )] <- paste(detdem[which(detdem$site_location == "" ),]$site_address, ", Detroit, MI, United States")
which(detdem$site_location == "" ) # nomore

# Extract lat/lon: if not present, then lat/lon is NA (817 rows).
detdemlatlon <- strsplit(gsub("[\\)\\( ]", "", str_extract(detdem$site_location, "\\(.*\\)")), ",")
length(which(is.na(detdemlatlon)))

geoind <- detdem[which(is.na(detdemlatlon)),]$site_location

# Add also address with wrong lat/lon
geoind <- append(geoind, gsub("\\n", " ", gsub("\\(.*\\)", "", detdem[which(detdem$lat > 43|detdem$lat < 42|detdem$lon < -84|detdem$lon > -81|is.na(detdem$lat)),]$site_location)))

# 14 obs have site_location 1= "", but without lat/lon. There is a /n in the string, to be removed. 

infile <- "detdem"

addresses <- geoind
length(addresses)

#initialise a dataframe to hold the results
geocoded <- data.frame()
# find out where to start in the address list (if the script was interrupted before):
startindex <- 1
#if a temp file exists - load it up and count the rows!
tempfilename <- paste0(infile, '_temp_geocoded.rds')
if (file.exists(tempfilename)){
  print("Found temp file - resuming from index:")
  geocoded <- readRDS(tempfilename)
  startindex <- nrow(geocoded)+1  # GC Editing to avoid duplicate
  print(startindex)
}

# Start the geocoding process - address by address. geocode() function takes care of query speed limit.
for (ii in seq(startindex, length(addresses))){
  print(paste("Working on index", ii, "of", length(addresses)))
  #query the google geocoder - this will pause here if we are over the limit.
  k = 1
  while (k < 6) {
  result = getGeoDetails(addresses[ii]) 
  if (!is.na(result$lat)) {
    result$index <- ii
    #append the answer to the results file.
    geocoded <- rbind(geocoded, result)
    #save temporary results as we are going along
    saveRDS(geocoded, tempfilename)
    k=6
  } else {
    k = k+1
    }
  }
}

if (any(is.na(geocoded))) {
  print(paste0("detdem - You looose...  ", as.character(length(which(is.na(geocoded$lat)))), " addresses not geocoded, addresses index ", toString(which(is.na(geocoded$lat)))))
  } else {
    print("detdem - Perfect! You win !!!")
    }

geocoded[which(is.na(geocoded$lat)),]
addresses[which(is.na(geocoded$lat))]

# Normalizing site_location adding the missing lat/lon
detdem$site_location[which(is.na(detdemlatlon))] <- paste0(detdem$site_location[which(is.na(detdemlatlon))], ", (", geocoded$lat, ", ", geocoded$long, ")")

# Normalizing also the wrong lat/lon
detdem$site_location[which(detdem$lat > 43|detdem$lat < 42|detdem$lon < -84|detdem$lon > -81|is.na(detdem$lat))] <- 
  paste0(gsub("\\n", " ", gsub("\\(.*\\)", "", detdem[which(detdem$lat > 43|detdem$lat < 42|detdem$lon < -84|detdem$lon > -81|is.na(detdem$lat)),]$site_location)), 
         ", (", geocoded$lat, ", ", geocoded$long, ")")

# Check that no more lat/lon is NA (0 rows).
length(which(is.na(strsplit(gsub("[\\)\\( ]", "", str_extract(detdem$site_location, "\\(.*\\)")), ","))))

# RE - Extract lat/lon: this time should be 0 NA.
detdemlatlon <- strsplit(gsub("[\\)\\( ]", "", str_extract(detdem$site_location, "\\(.*\\)")), ",")
length(which(is.na(detdemlatlon)))

detdem$lat <- sapply(detdemlatlon, "[[", 1)
detdem$lon <- sapply(detdemlatlon, "[[", 2)
detdem$lat <- as.numeric(detdem$lat)
detdem$lon <- as.numeric(detdem$lon)

# No more wrong values.
detdem[which(detdem$lat > 43|detdem$lat < 42|detdem$lon < -84|detdem$lon > -81|is.na(detdem$lat)),]$site_location

#Write it all to the output files
saveRDS(detdem, "detdem_geocoded.rds")
write.table(detdem, "detdem_geocoded.csv", sep=",", row.names=T)

# If detdem already normalized and saved
detdem <- readRDS("detdem_geocoded.rds")



#############################################################
#                                                           #
# Extract lat/lon fot detcrime.                             #
#     NOTE: detcrime has 59 obs without lat/lon.            #
#           and 373 lat lon wrong                           #
#############################################################
nrow(detcrime[which(is.na(as.numeric(detcrime$lat))),])

# summary(detdem$lat)
# summary(detviol$lat)
# summary(det311$lat)
# 
# summary(detdem$lon)
# summary(detviol$lon)
# summary(det311$lon)
# summary(detcrime$lat)

nrow(detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),])

# Extract lat/lon: If not present, then lat/lon is NA (30 rows). This means that 30 put of 59 obs without lat/lon,
#                  in addition do not have lat/lon even in location.
#                  To be geocoded from address.
detcrimelatlon <- strsplit(gsub("[\\)\\( ]", "", str_extract(detcrime$location, "\\(.*\\)")), ",")
nrow(detcrime[which(is.na(detcrimelatlon)),])

# First, updating location with goecoded lat/lon: 
# Normalize the location: Adding Detroit, Mi, United States to address, removing ^00, updating location with address.
detcrime$address <- paste(detcrime$address , ", Detroit, MI, United States")
detcrime$address <- gsub("^00 ", "", detcrime$address, "\\(.*\\)")

#detcrime[which(is.na(as.numeric(detcrime$lat))),]

# Put address in location ONLY where location does not include lat/lon
detcrime$location[which(is.na(detcrimelatlon))]  <- detcrime$address[which(is.na(detcrimelatlon))] 

geoind <- detcrime$location[which(is.na(detcrimelatlon))]


# Geocoding script for large list of addresses (30 rows, here).
# Shane Lynn 10/10/2013

infile <- "detcrime"
addresses <- geoind

#initialise a dataframe to hold the results
geocoded <- data.frame()
# find out where to start in the address list (if the script was interrupted before):
startindex <- 1
#if a temp file exists - load it up and count the rows!
tempfilename <- paste0(infile, '_temp_geocoded.rds')
if (file.exists(tempfilename)){
  print("Found temp file - resuming from index:")
  geocoded <- readRDS(tempfilename)
  startindex <- nrow(geocoded)+1  # GC Editing to avoid duplicate
  print(startindex)
}

# Start the geocoding process - address by address. geocode() function takes care of query speed limit.
for (ii in seq(startindex, length(addresses))){
  print(paste("Working on index", ii, "of", length(addresses)))
  #query the google geocoder - this will pause here if we are over the limit.
  k = 1
  while (k < 6) {
    result = getGeoDetails(addresses[ii]) 
    if (!is.na(result$lat)) {
      result$index <- ii
      #append the answer to the results file.
      geocoded <- rbind(geocoded, result)
      #save temporary results as we are going along
      saveRDS(geocoded, tempfilename)
      k=6
    } else {
      k = k+1
    }
  }
}

if (any(is.na(geocoded))) {
  print(paste0("detcrime - You looose...  ", as.character(length(which(is.na(geocoded$lat)))), " addresses not geocoded, addresses index ", toString(which(is.na(geocoded$lat)))))
} else {
  print("detcrime - Perfect! You win !!!")
}
# Normalizing site_location adding the missing lat/lon
detcrime$location[which(is.na(detcrimelatlon))] <- paste0(detcrime$location[which(is.na(detcrimelatlon))], ", (", geocoded$lat, ", ", geocoded$long, ")")


# Check that all 30 obs have lat/lon geocoded. 
detcrime[which(is.na(detcrimelatlon)),]

# Now, we can extraxt all the 59 lat/lon missing from location
detcrimelatlon <- strsplit(gsub("[\\)\\( ]", "", str_extract(detcrime[which(is.na(detcrime$lat)),]$location, "\\(.*\\)")), ",")
#detcrime[which(is.na(detcrime$lat)),]$location
length(detcrimelatlon)
detcrimelatlon[which(is.na(detcrimelatlon))]
# Row 32 is wrong. Cleaning
detcrimelatlon[[32]] <- detcrimelatlon[[32]][5:6]

detcrime[which(is.na(detcrime$lat)),]$lat <- sapply(detcrimelatlon, "[[", 1)
detcrime[which(is.na(detcrime$lon)),]$lon <- sapply(detcrimelatlon, "[[", 2)
detcrime$lat <- as.numeric(detcrime$lat)
detcrime$lon <- as.numeric(detcrime$lon)

# Normalizing WRONG lat lon in detcrime.
nrow(detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),])

geoind <- detcrime$address[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80)]

# Geocoding script for large list of addresses (30 rows, here).
# Shane Lynn 10/10/2013

geoind <- gsub("&", " ", geoind) #  Google API has difficulty to manage the "&" char.

infile <- "detcrime"
addresses <- geoind

#initialise a dataframe to hold the results
geocoded <- data.frame()
# find out where to start in the address list (if the script was interrupted before):
startindex <- 1
#if a temp file exists - load it up and count the rows!
tempfilename <- paste0(infile, '_temp_geocoded.rds')
if (file.exists(tempfilename)){
        print("Found temp file - resuming from index:")
        geocoded <- readRDS(tempfilename)
        startindex <- nrow(geocoded)+1  # GC Editing to avoid duplicate
        print(startindex)
}

# Start the geocoding process - address by address. geocode() function takes care of query speed limit.
for (ii in seq(startindex, length(addresses))){
        print(paste("Working on index", ii, "of", length(addresses)))
        #query the google geocoder - this will pause here if we are over the limit.
        k = 1
        while (k < 16) {
                result = getGeoDetails(addresses[ii]) 
                if (!is.na(result$lat)) {
                        result$index <- ii
                        #append the answer to the results file.
                        geocoded <- rbind(geocoded, result)
                        #save temporary results as we are going along
                        saveRDS(geocoded, tempfilename)
                        k=16
                } else {
                        k = k+1
                }
        }
}

if (any(is.na(geocoded))) {
        print(paste0("detcrime - You looose...  ", as.character(length(which(is.na(geocoded$lat)))), " addresses not geocoded, addresses index ", toString(which(is.na(geocoded$lat)))))
} else {
        print("detcrime - Perfect! You win !!!")
}

detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),]$lat <- geocoded$lat
detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),]$lon <- geocoded$long

nrow(detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),])
# deleting 19 too far lat lon 
detcrime <- detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),]
nrow(detcrime[which(detcrime$lat < 41.88 | detcrime$lat > 42.75 | detcrime$lon < -83.32 | detcrime$lon > -82.80),])

#finally write it all to the output files
saveRDS(detcrime, "detcrime_geocoded.rds")
write.table(detcrime, "detcrime_geocoded.csv", sep=",", row.names=T)

# If detcrime already normalized and saved
detcrime <- readRDS("detcrime_geocoded.rds")




##################################################################
###  NORMALIZING THE DATEs AMONG ALL THE DATASETS              ###
###     NOTE: The period of time is incomarable because        ###
###           very different condition in occupation,          ###
###           social and economic condition                    ###
###         So, build 2 model,one with,and one without         ###
###         the date in different period among datasets.       ###
##################################################################
# Date detdem
detdem$demdate     <- as.Date(detdem$permit_applied, "%m/%d/%y")
detcrime$crimedate <- as.Date(detcrime$incidentdate, "%m/%d/%Y %I:%M:%S %p") # "09/02/2015 12:00:00 AM"

# Date detviol
# NOTE: Some dates in detviol have 1900 base date AS YEAR. Extract year and normalize date.
#       Then, Use only date starting from min demolition permits.

# Normalize gooddate as yyyy-mm-dd as char to vectorize operation.
detviol[which(as.numeric(substr(detviol$ticketissueddt, 7,11)) < 2017),]$violdate <- as.character(as.Date(detviol[which(as.numeric(substr(detviol$ticketissueddt, 7,11)) < 2017),]$ticketissueddt, "%m/%d/%Y %I:%M:%S %p"))
detviol[307700:307804,]$violdate

# Date normali ok. Sistemare quelle anno 1900.
detviol[which(as.numeric(substr(detviol$ticketissueddt, 7,11)) > 9999),]$violdate <- as.character(as.Date(as.numeric(substr(detviol[which(as.numeric(substr(detviol$ticketissueddt, 7,11)) > 9999),]$ticketissueddt,7,11)), origin = "1900-01-01"))

detviol$violdate <- as.Date(detviol$violdate)

# dates <- c("05/27/84", "07/07/05", "08/17/20")
# betterDates <- as.Date(dates, "%m/%d/%y")
# 
# > betterDates
# [1] "1984-05-27" "2005-07-07" "2020-08-17"
# 
# correctCentury <- as.Date(ifelse(betterDates > Sys.Date(), 
#                                  format(betterDates, "19%y-%m-%d"), 
#                                  format(betterDates)))
# > correctCentury
# [1] "1984-05-27" "2005-07-07" "1920-08-17"

str(det311) # ticket_created_date_time
nrow(det311)
max(det311$ticket_created_date_time)
det311$date311 <- as.Date(det311$ticket_created_date_time, "%m/%d/%Y %I:%M:%S %p") # "09/02/2015 12:00:00 AM"

##################################################################
###  REMOVE OUTLIERS FROM OTHERS DATASETS.                     ###
###                                                            ###
##################################################################
detdem   <- detdem[which(detdem$lat     < 42.45 & detdem$lat   > 42.25 & detdem$lon   > -83.35 & detdem$lon   < -82.90),]
detcrime <- detcrime[which(detcrime$lat < 42.45 & detcrime$lat > 42.25 & detcrime$lon > -83.35 & detcrime$lon < -82.90),]
detviol  <- detviol[which(detviol$lat   < 42.45 & detviol$lat  > 42.25 & detviol$lon  > -83.35 & detviol$lon  < -82.90),]
det311   <- det311[which(det311$lat     < 42.45 & det311$lat   > 42.25 & det311$lon   > -83.35 & det311$lon   < -82.90),]

saveRDS(detdem,   "detdem_geocoded_date.rds")
saveRDS(detviol,  "detviol_geocoded_date.rds")
saveRDS(detcrime, "detcrime_geocoded_date.rds")
saveRDS(det311,   "det311_geocoded_date.rds")




################################################
################################################
##                                            ##
## Building a complete dataset incident       ##
## with label for blighted building           ##
##                                            ##
################################################
################################################
# detdem   <- readRDS("detdem_geocoded_date.rds")
# detviol  <- readRDS("detviol_geocoded_date.rds")
# detcrime <- readRDS("detcrime_geocoded_date.rds")
# det311   <- readRDS("det311_geocoded_date.rds")

# First compute the cluster for each dataset. NO. all togheter.
# detdem_modelcl    <- leaderCluster(data.frame(lat=detdem$lat,   lon=detdem$lon),   radius = 1.5, distance = "haversine")
# detviol_modelcl   <- leaderCluster(data.frame(lat=detviol$lat,  lon=detviol$lon),  radius = 1.5, distance = "haversine")
# det311_modelcl    <- leaderCluster(data.frame(lat=det311$lat,   lon=det311$lon),   radius = 1.5, distance = "haversine")
# detcrime_modelcl  <- leaderCluster(data.frame(lat=detcrime$lat, lon=detcrime$lon), radius = 1.5, distance = "haversine")

# detdem$cluster_id   <- detdem_modelcl[[1]]
# detviol$cluster_id  <- detviol_modelcl[[1]]
# det311$cluster_id   <- det311_modelcl[[1]]
# detcrime$cluster_id <- detcrime_modelcl[[1]]




###################################################################
###################################################################
###                                                             ###
###  CREATING  A LIST OF BUILDINGS WITH GEO INFO IDENTIFIERS    ###
###                                                             ###
###  NOTE:                                                      ###    
###         1. CLUSTERING DETDEM                                ###
###         2. CREATE BUILDING WITH ALPHASHAPE FOR DETDEM       ###
###         3. ASSIGN TO EACH LOCATION OF OTHERS INCIDENTS TYPE ###
###            THE SAME CLUSTER OF THE BUILDING OF DETDEM       ###
###                                                             ###
###################################################################
###################################################################
detdem   <- readRDS("detdem_geocoded_date.rds")
detviol  <- readRDS("detviol_geocoded_date.rds")
detcrime <- readRDS("detcrime_geocoded_date.rds")
det311   <- readRDS("det311_geocoded_date.rds")

# nrow(detcrime)
# nrow(det311)
# 
# unique(detdem$cluster_id)

# Find the current range of x and y.    
# ggplot_build(lcp)$panel$ranges[[1]]$y.range
# ggplot_build(lcp)$panel$ranges[[1]]$x.range

# NOTE: Is it not possible to cluster all the incidents, because the complete fullfill.  
#     
# str(detdem)
# str(detviol)
# str(detcrime)
# str(det311)
# 



##################################################################
###  1. CREATING CLUSTER AND PLOTTING DEMOLITION DATA          ###
###         AGAINST POIs.                                      ###
###                                                            ###
###     NOTE: leaderCluster perform better then DBSCAN         ###
###                                                            ###
##################################################################
# Compute radius of Earth to Detroit latitude for Haversine : (value ??)
# radiusdetroit = sqrt( (  (6378137^2 * cos(42.331429))^2 + (6356752^2 * sin(42.331429))^2 ) /
#                           ( (6378137 * cos(42.331429))^2 + (6356752 * sin(42.331429))^2 ) )
#
detdem   <- readRDS("detdem_geocoded_date.rds")
detdem_modelcl  <- leaderCluster(data.frame(lat=detdem$lat, lon=detdem$lon), radius = .3, distance = "haversine")
detdem$cluster_id <- detdem_modelcl[[1]]
str(detdem_modelcl)
str(detcrime) # PROVARE MAPPOI PURE QUI.
lc_centroids <- as.data.frame(detdem_modelcl$cluster_centroids)
lc_centroids$cluster_id <- seq(1:nrow(detdem_modelcl$cluster_centroids))
names(lc_centroids) <- c("lat", "lon", "cluster_id")
# str(lc_centroids)

poi <- c("business", "government", "medical", "park", "school", "sports_complex")
savemappoi(poi, detdem)




################################################################
#                                                              #
# Create and plotting SpatialPolygonsDataFrame                 #          
# as convex hull                                               #       
#  NOTE: GOOD CLUSTERING BUT NO SEARCH SIMPLE                  #
#                                                              #
################################################################
# Create list of chull (lat/lon) for each cluster
# ch <- list()
# for (c in unique(incidents$cluster_id)) {
#         clpoints <- data.frame(lat=incidents[(which(incidents$cluster_id == c)),]$lat, 
#                                lon=incidents[(which(incidents$cluster_id == c)),]$lon) 
#         ch[[paste0("ch",c)]] <- clpoints[c(chull(clpoints), chull(clpoints)[1]), ]
# }
# savemapchull(ch)
# 
# summary(incidents[which(incidents$cluster_id == 109),]$lat)
# str(incidents)




################################################################
#                                                              #
# Create and plotting SpatialPolygonsDataFrame                 #          
# as alpha convex hull                                         #
#                                                              #
################################################################

# Create list of ahull of type alpha shape for each cluster
# Each data frame of the list, contains the polygon coordinates of the alpha shape for that cluster

# Script to plot an alpha shape on ggplot2 from a given sets of points
# Inspired by: https://rpubs.com/geospacedman/alphasimple

# Normalize lat lon
detdem$lat <- round(detdem$lat, 11)
detdem$lon <- round(detdem$lon, 11)

# Remove duplicated points - only for creating hull purpoise
detdem$latlon <- paste(as.character(detdem$lat), as.character(detdem$lon))
detdem_nodup <- detdem[-c(which(duplicated(detdem$latlon))), ]

# remove cluster  with less then 3 points - ONLY FOR CREATING HULL PURPOISE
ft <- data.frame(table(detdem_nodup$cluster_id))
ft
ft <- ft[which(ft$Freq > 2 ),]$Var1
ft
# detdem_nodup <- detdem_nodup[which(detdem_nodup$cluster_id %in% ft),]
nrow(detdem_nodup)



# Debug 300 meters buildings. : All the error gone away once I manually executed ( JIt compiled) the haull function.

# # Non servono.
# # cluster 9.
# data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  9)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == 9)),]$lon)
# plot(data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  9)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == 9)),]$lon) )
# detdem_nodup <- detdem_nodup[-which(detdem_nodup$lat == 42.405256219 & detdem_nodup$lon == -82.957512005),]
# # cluster 24.
# coord <- data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  24)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == 24)),]$lon)
# coord
# plot(coord)
# detdem_nodup <- detdem_nodup[-which(detdem_nodup$lat == 42.332503089 & detdem_nodup$lon == -83.049753620),]
# # cluster 85.
# coord <- data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  85)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == 85)),]$lon)
# coord
# plot(coord)
# detdem_nodup[which(detdem_nodup$lat == 42.369037 & detdem_nodup$lon == -83.116876),]
# detdem_nodup <- detdem_nodup[-which(detdem_nodup$lat == 42.369037 & detdem_nodup$lon == -83.116876),]
# # cluster 101.
# coord <- data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  101)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == 101)),]$lon)
# coord
# plot(coord, type = "l")
# plot(coord)
# lat = 42.446259000
# lon = -83.094119000
# detdem_nodup[which(detdem_nodup$lat == lat & detdem_nodup$lon == lon),]
# detdem_nodup <- detdem_nodup[-which(detdem_nodup$lat == lat  & detdem_nodup$lon == lon),]

# cluster 106. Non usato e ha funzionato
# clu <- 106
# coord <- data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  clu)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == clu)),]$lon) 
# coord
# plot(coord, type = "l")
# plot(coord)
# lat = 42.446259000
# lon = -83.094119000
# detdem_nodup[which(detdem_nodup$lat == lat & detdem_nodup$lon == lon),]
# detdem_nodup <- detdem_nodup[-which(detdem_nodup$lat == lat  & detdem_nodup$lon == lon),]


# Compute centroids without outliers
ashape_centroids <- lc_centroids[which(lc_centroids$cluster_id %in% ft),]
ash <- list()
ahu <- list()
for (c in ft) {
    print(paste("elaboro : ", c))
    # Extract points by cluster.c=101
    # clpoints <-  as.data.frame(remove.duplicates(SpatialPoints((data.frame(lat=detdem[(which(detdem$cluster_id ==  c)),]$lat, lon=detdem[(which(detdem$cluster_id == c)),]$lon)))))
    clpoints <-  data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  c)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == c)),]$lon)        
    
    # Computation And Order Alpha Shape -------------------------------------------
    cl_ahull = ahull(clpoints, alpha = 2)
    cl_ashape = cl_ahull$ashape.obj
    # Take the coordinates of points on the edges of the alpha shape (as.character to not lost the order!)
    cl_mat = cl_ashape$edges[, c("ind1", "ind2")]
    # Convert 'numeric' matrix to 'character' matrix, to avoid wrong node orders 
    # (Otherwise 'graph.edgelist()' interprets number as order of nodes)
    class(cl_mat) = "character"
    # Make the graph of points
    cl_graph = graph.edgelist(cl_mat, directed = F)
    # Cut open the graph to walk through it in order
    cut_graph = cl_graph - E(cl_graph)[1]  # Cut the first edge
    ends = names(which(degree(cut_graph) == 1))   # Get two nodes with degree = 1        
    # Compute a path
    path = get.shortest.paths(cut_graph, ends[1], ends[2])$vpath[[1]]
    # Get node names (= row numbers in original data.frame)
    path_nodes = as.numeric(V(cl_graph)[path]$name)
    # Compute a path
    ash[[paste0("ash",c)]] <- clpoints[path_nodes, ]
    ahu[[paste0("ahu",c)]] <- cl_ahull
    # print so:   +  geom_polygon(data = ex[path_nodes, ], fill = "purple", alpha = 0.5)
}

# 614 ahull freq > 2.
# All derived from detdem.
length(ash) 

    
    cluster_freq <- data.frame()
    for (c in ft) {
        clpoints <-  data.frame(lat=detdem_nodup[(which(detdem_nodup$cluster_id ==  c)),]$lat, lon=detdem_nodup[(which(detdem_nodup$cluster_id == c)),]$lon)        
        freq <- nrow(clpoints)
        freq_clpoints <- cbind(clpoints, freq)[1,]
        cluster_freq <- rbind(cluster_freq, freq_clpoints)
    }
    cluster_freq
    
    savemapashape(ash)
    
    # coords = c(42.39, -83.70  )
    # b = "ahu1"
    # plot(ahu[["ahu1"]])

getbuildings <- function(coords, blist) {
        buildingslist <- c()
        for (b in names(blist)) {
                # IMPORTANT : inahull works only in the plane of coordinates of current hull
                # Check if coords are in plane, otherwise, skip.
                if (abs(coords[1]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
                    abs(coords[1]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
                    abs(coords[2]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) &
                    abs(coords[2]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) ) {
                        if (inahull(ahu[[b]], p = coords))  {
                                buildingslist <- c(buildingslist, b)        
                        }
                }
        }
        if (length(buildingslist) == 0) {
                buildingslist <- c(buildingslist, "no_cluster") 
        }
        return(buildingslist)                        
}


getbuildings(c(42.43000232323, -82.97000233323  ), ahu)
getbuildings(c(42.445890285, -82.987933397), ahu)
getbuildings(c(42.441023443, -83.0234533345  ), ahu)
getbuildings(c(42.39, -82.96  ), ahu)


# assign_buildings <- function(coords, blist) {
#     buildingslist <- c()
#     for (b in names(blist)) {
#         # IMPORTANT : inahull works only in the plane of coordinates of current hull
#         # Check if coords are in plane, otherwise, skip.
#         if (abs(coords[1]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#             abs(coords[1]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#             abs(coords[2]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) &
#             abs(coords[2]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) ) {
#             if (inahull(ahu[[b]], p = coords))  {
#                 buildingslist <- c(buildingslist, as.numeric(gsub("ahu", "", b )) )        
#             }
#         }
#     }
#     if (length(buildingslist) == 0) {
#         buildingslist <- c(buildingslist, 0) 
#     }
#     return(buildingslist)                        
# }



# Assign building as atomic abject.
assign_buildings <- function(coords, blist) {
    buildingslist <- c()
    for (b in names(blist)) {
        # IMPORTANT : inahull works only in the plane of coordinates of current hull
        # Check if coords are in plane, otherwise, skip.
        if (abs(coords[1]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
            abs(coords[1]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
            abs(coords[2]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) &
            abs(coords[2]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) ) {
            if (inahull(ahu[[b]], p = coords))  {
                buildingslist <- paste(buildingslist, b)
            }
        }
    }
    if (length(buildingslist) == 0) {
        buildingslist <- "!ahu"
    }
    return(buildingslist)
}

# count_buildings_assigned <- function(coords, blist) {
#     n_buildings <- 0
#     for (b in names(blist)) {
#         # IMPORTANT : inahull works only in the plane of coordinates of current hull
#         # Check if coords are in plane, otherwise, skip.
#         if (abs(coords[1]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#             abs(coords[1]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#             abs(coords[2]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) &
#             abs(coords[2]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) ) {
#             if (inahull(ahu[[b]], p = coords))  {
#                 n_buildings <- n_buildings + 1         
#             }
#         }
#     }
#     # if (length(buildingslist) == 0) {
#     #     buildingslist <- c(buildingslist, 0) 
#     # }
#     return(n_buildings)                        
# }


# Varie prove su erroe di non aver ricalcolato il cluster di detdem
# 
# count_buildings_assigned(c(42.445890285, -82.987933397), ahu["ahu13"])
# 
# inahull(ahu["ahu13"], c(42.445890285, -82.987933397))
# 
# 
# detdem[which(detdem$lat == 42.445890285),]
# 
# 
# b = "ahu13"
# coords = c(42.445890285, -82.987933397)
# (abs(coords[1]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#     abs(coords[1]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#     abs(coords[2]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) &
#     abs(coords[2]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) ) 
# 
# inahull(ahu["ahu13"], c(42.445890285, -82.987933397))
# count_buildings_assigned(c(42.445890285, -82.987933397), ahu["ahu13"])
# 
# 
# 
# 
# detdem[which(detdem$lat == 42.445890285),]
# inahull(ahu["ahu13"], c(42.44589    , -82.98793    ))
# coords <- c(42.445890285, -82.987933397) 
# b <- "ahu13"
# abs(coords[1]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#     abs(coords[1]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,3])) &
#     abs(coords[2]) >= min(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) &
#     abs(coords[2]) <= max(abs(ahu[[b]][["ashape.obj"]][["edges"]][,4])) 
# 

# count_buildings_assigned(c(42.445890285, -82.987933397), ahu["ahu13"])
# inahull(ahu[["ahu13"]], p = coords)
# detdem[which(detdem$lat == 42.445890285 & detdem$lon == -82.987933397),]

# plot(ahu[["ahu3"]])
# 
# str(ahu[["ahu4"]])
# 
# min(ahu[["ahu4"]][["ashape.obj"]][["edges"]][,3])
# max(ahu[["ahu4"]][["ashape.obj"]][["edges"]][,3])
# 
# min(ahu[["ahu4"]][["ashape.obj"]][["edges"]][,4])
# max(ahu[["ahu4"]][["ashape.obj"]][["edges"]][,4])




################################################################
#                                                              #
# DATES HAVE TO BE ALL INCLUDED BECAUSE IT'S NORMAL THAT       #
# VIOL-VIOL-VIOL-VIOL, THEN CLUSTER (SOME YEARS LATER!)        #
#                                                              #
################################################################





################################################################
#                                                              #
# Assign one or more cluster to each point of other datasets:  #
#     a. cluster_id if found.                                  #
#     b. cluster 0 if not found                                #
################################################################

#################################################################
# detdem already has the cluster_id column, but it is the       #
# original, numeric one, inlcuding cluster with less then three #
# locations. Normalize detdem cluster_id with the same          #
# classification as the others datasets.                        # 
#                                                               #
#################################################################
detdem  <- readRDS("detdem_geocoded_date.rds")
res <- apply(data.frame(detdem$lat, detdem$lon), 1, assign_buildings, ahu)
detdem$cluster_id <- res
# Check locations with multiple cluster.
detdem[which(round(detdem$lat, 2) == 42.39 & round(detdem$lon, 2) == -82.96),][1:10,]

# detviol
detviol  <- readRDS("detviol_geocoded_date.rds")
res <- apply(data.frame(detviol$lat, detviol$lon), 1, assign_buildings, ahu)
detviol$cluster_id <- res
# Check locations with multiple cluster.
detviol[which(round(detviol$lat, 2) == 42.39 & round(detviol$lon, 2) == -82.96),][1:10,]

# detcrime
detcrime  <- readRDS("detcrime_geocoded_date.rds")
res <- apply(data.frame(detcrime$lat, detcrime$lon), 1, assign_buildings, ahu)
detcrime$cluster_id <- res
# Check locations with multiple cluster.
detcrime[which(round(detcrime$lat, 2) == 42.39 & round(detcrime$lon, 2) == -82.96),][1:10,]

# det311
det311  <- readRDS("det311_geocoded_date.rds")
res <- apply(data.frame(det311$lat, det311$lon), 1, assign_buildings, ahu)
det311$cluster_id <- res
# Check locations with multiple cluster.
det311[which(round(det311$lat, 2) == 42.39 & round(det311$lon, 2) == -82.96),][1:10,]

str(det311)

saveRDS(detdem,   "detdem_geocoded_clustered_3_date.rds")
saveRDS(detviol,  "detviol_geocoded_clustered_3_date.rds")
saveRDS(detcrime, "detcrime_geocoded_clustered_3_date.rds")
saveRDS(det311,   "det311_geocoded_clustered_3_date.rds")

detdem    <- readRDS("detdem_geocoded_clustered_3_date.rds")
detviol   <- readRDS("detviol_geocoded_clustered_3_date.rds")
detcrime  <- readRDS("detcrime_geocoded_clustered_3_date.rds")
det311    <- readRDS("det311_geocoded_clustered_3_date.rds")


# ################################################################
# # Count how many cluster assigned to each location. NO         #
# ################################################################
# #dem
# res <- apply(data.frame(detdem$lat, detdem$lon), 1, count_buildings_assigned, ahu)
# detdem$n_buildings <- res
# table(detdem$n_buildings)
# 
# #viol
# res <- apply(data.frame(detviol$lat, detviol$lon), 1, count_buildings_assigned, ahu)
# detviol$n_buildings <- res
# table(detviol$n_buildings)
# 
# #crime
# res <- apply(data.frame(detcrime$lat, detcrime$lon), 1, count_buildings_assigned, ahu)
# detcrime$n_buildings <- res
# table(detcrime$n_buildings)
# 
# #311
# res <- apply(data.frame(det311$lat, det311$lon), 1, count_buildings_assigned, ahu)
# det311$n_buildings <- res
# table(det311$n_buildings)
# 
# saveRDS(detdem,  "detdem_geocoded__clustered_3_date_nbuild.rds")
# saveRDS(detviol,  "detviol_geocoded__clustered_3_date_nbuild.rds")
# saveRDS(detcrime, "detcrime_geocoded_clustered_3_date_nbuild.rds")
# saveRDS(det311,   "det311_geocoded_clustered_3_date_nbuild.rds")
# 
# # NOTE
# # NOTE
# # NOTE
# #      Dataset to be created: lat, lon, cluster_id, n_luster(0,1,2), nviol, ncrime, n311 
# # NOTE
# # NOTE
# # NOTE
# 
# detdem   <- readRDS("detdem_geocoded__clustered_3_date_nbuild.rds")
# detviol  <- readRDS("detviol_geocoded__clustered_3_date_nbuild.rds")
# detcrime <- readRDS("detcrime_geocoded_clustered_3_date_nbuild.rds")
# det311   <- readRDS("det311_geocoded_clustered_3_date_nbuild.rds")
# 
# detdem[which(round(detdem$lat, 2) == 42.39 & round(detdem$lon, 2) == -82.96),]
# det311[which(round(det311$lat, 2) == 42.39 & round(det311$lon, 2) == -82.96),]



# OK. Fondamentalmente fino a qui OK. Niente n_buildings. Usare tutte le freq e basta. 


###############################################################   
#                                                             # 
# Add cluster weigth (freq of location in cluster) to dataset # 
#                                                             # 
###############################################################   
# detviol
freq <- as.data.frame(table(detviol$cluster_id))
detviol <- merge(detviol, freq, by.x = "cluster_id", by.y = "Var1", all.x = T)
# Reorder
detviol <- detviol[,c(2:ncol(detviol), 1)]
str(detviol)

# detcrime
freq <- as.data.frame(table(detcrime$cluster_id))
detcrime <- merge(detcrime, freq, by.x = "cluster_id", by.y = "Var1", all.x = T)
# Reorder
detcrime <- detcrime[,c(2:ncol(detcrime), 1)]
str(detcrime)

# det311
freq <- as.data.frame(table(det311$cluster_id))
det311 <- merge(det311, freq, by.x = "cluster_id", by.y = "Var1", all.x = T)
# Reorder
det311 <- det311[,c(2:ncol(det311), 1)]
str(det311)

# detdem
freq <- as.data.frame(table(detdem$cluster_id))
detdem <- merge(detdem, freq, by.x = "cluster_id", by.y = "Var1", all.x = T)
# Reorder
detdem <- detdem[,c(2:ncol(detdem), 1)]
str(detdem)

colnames(detviol) <- tolower(colnames(detviol))
colnames(detcrime) <- tolower(colnames(detcrime))
colnames(det311) <- tolower(colnames(det311))
colnames(detdem) <- tolower(colnames(detdem))

saveRDS(detdem,  "detdem_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")
saveRDS(detviol,  "detviol_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")
saveRDS(detcrime, "detcrime_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")
saveRDS(det311,   "det311_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")




###############################################################################################################
# Remove duplicate lat lon for unique buildings:                                                              #
# NOTE : Now, we have the frequence for each cluster, that inludes how many locations are in that cluster.    #
#        Therefore, we can identify the unique buildings by unique lat lon, without loss the frequency  info. #
###############################################################################################################   
detdem   <- readRDS("detdem_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")
detviol  <- readRDS("detviol_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")
detcrime <- readRDS("detcrime_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")
det311   <- readRDS("det311_geocoded_clustered_3_date_nbuild_f_recomputed_300m.rds")

nrow(detdem)
nrow(detcrime)
nrow(detviol)
nrow(det311)

str(detdem)
str(detcrime)
str(detviol)
str(det311)

# Remove duplicated points in detdem
detdem$latlon <- paste(as.character(detdem$lat), as.character(detdem$lon))
detdem <- detdem[-c(which(duplicated(detdem$latlon))), ]
nrow(detdem)

# Remove duplicated points in detcrime
detcrime$latlon <- paste(as.character(detcrime$lat), as.character(detcrime$lon))
detrime <- detcrime[-c(which(duplicated(detcrime$latlon))), ]
nrow(detcrime)

# Remove duplicated points in detviol
detviol$latlon <- paste(as.character(detviol$lat), as.character(detviol$lon))
detviol <- detviol[-c(which(duplicated(detviol$latlon))), ]
nrow(detviol)

# Remove duplicated points in det311
det311$latlon <- paste(as.character(det311$lat), as.character(det311$lon))
det311 <- det311[-c(which(duplicated(det311$latlon))), ]
nrow(det311)

saveRDS(detdem,   "detdem_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")       #   5719 rows.
saveRDS(detviol,  "detviol_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")      #  96314 rows.
saveRDS(detcrime, "detcrime_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")      # 119742 rows.
saveRDS(det311,   "det311_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")        #  17278 rows.

# Binding datasets

detdem   <- readRDS("detdem_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")
detviol  <- readRDS("detviol_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")
detcrime <- readRDS("detcrime_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")
det311   <- readRDS("det311_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")




# Being that we have to sample 7132 rows, it worths to sample only the most recent, and demolition aligned rows.
# Therefore, we filter the datasets per same data.  NO. Too few detdem for 2015.



#####################################################################
#                                                                   # 
# train a simple model only on clustering by haversine distance     #
# using only detviol$freq.                                          #
#                                                                   # 
#####################################################################
# The viol in the cluster = 0 are not blighted, because they do not belong to a building.
events <- data.frame(type = "detviol", 
                     lat = detviol$lat, 
                     lon = detviol$lon, 
                     cluster_id = detviol$cluster_id, 
                     freq = detviol$Freq)

events$label <- ""
events[which(events$cluster_id == 0),]$freq <- 1
events[which(events$cluster_id == 0),]$label <- "not_blight"
events[which(events$cluster_id != 0),]$label <- "blight"

trainIndex <- createDataPartition(events$label, p = .5,
                                  list = FALSE,
                                  times = 1)

eventstrain <- events[trainIndex,]
eventstest  <- events[-trainIndex,]

fitControl <- trainControl(## 5-fold CV
    method = "repeatedcv",
    number = 5,
    repeats = 5)
# ,sampling = "down")

eventstrain[1:10,]
eventstrain$label <- factor(eventstrain$label)
glmfit1 <- train(label ~ freq, data = eventstrain,
                 method = "bayesglm",
                 trControl = fitControl,
                 family = "quasibinomial")

glmfit1  
summary(glmfit1)

summary(factor(eventstest$label))
summary(factor(eventstrain$label))
table(eventstrain$freq)

eventstest1 <- eventstest
eventstest1$label <- NULL
str(eventstest1)

eventstest1[1:10,]

predglm <- predict(glmfit1, newdata=eventstest1)
confusionMatrix(predglm, eventstest$label)

eventsneg <- eventstest[which(events$cluster_id == "!ahu"),]
eventsneg[1:10,]
predglm <- predict(glmfit1, newdata=eventsneg)
confusionMatrix(predglm, eventsneg$label)


#####################################################################
#                                                                   # 
# ENGENEERING NEW FEATURES                                          #
#                                                                   #
#                                                                   # 
#####################################################################

################################################
# 1. Adding average judgmentamt per building   #
################################################
nrow(detdem)
nrow(detviol)
nrow(detcrime)
nrow(det311)

allevents <- rbind(
    data.frame(type = "detdem", 
               lat = detdem$lat, 
               lon = detdem$lon, 
               cluster_id = detdem$cluster_id, 
               freq = detdem$freq),
    data.frame(type = "detviol", 
               lat = detviol$lat, 
               lon = detviol$lon, 
               cluster_id = detviol$cluster_id, 
               freq = detviol$freq),
    data.frame(type = "detcrime", 
               lat = detcrime$lat, 
               lon = detcrime$lon, 
               cluster_id = detcrime$cluster_id, 
               freq = detcrime$freq),
    data.frame(type = "det311", 
               lat = det311$lat, 
               lon = det311$lon, 
               cluster_id = det311$cluster_id, 
               freq = det311$freq)
)

detviol$judgmentamt <- as.numeric(sub("\\$","", detviol$judgmentamt))
detviol$judgmentamt[which(is.na(detviol$judgmentamt))] <- 0

avg_judg <- aggregate(detviol[, "judgmentamt"], list(cluster_id = as.character(detviol$cluster_id)), mean)

allevents <- merge(allevents, avg_judg, by.x = "cluster_id", by.y = "cluster_id")  # on all datasets
colnames(allevents)[6] <- "avg_judg"





##########################################################
# 2. Adding number of incidents (311 calls) per cluster  #
##########################################################
count_311 <- aggregate((det311$cluster_id), list(cluster_id=as.character(det311$cluster_id)), length)
count_311

allevents <- merge(allevents, count_311, by.x = "cluster_id", by.y = "cluster_id")  # on all datasets
colnames(allevents)[7] <- "count_311"
str(allevents)





##########################################################
# 3. Adding number of incidents (crime) per cluster      #
##########################################################
count_crime <- aggregate((detcrime$cluster_id), list(cluster_id=as.character(detcrime$cluster_id)), length)
count_crime

allevents <- merge(allevents, count_crime, by.x = "cluster_id", by.y = "cluster_id")  # on all datasets
colnames(allevents)[8] <- "count_crime"
str(allevents)





##########################################################
# 4. Adding number of incidents (violation) per cluster  #
##########################################################
count_viol <- aggregate((detviol$cluster_id), list(cluster_id=as.character(detviol$cluster_id)), length)
count_viol

allevents <- merge(allevents, count_viol, by.x = "cluster_id", by.y = "cluster_id")  # on all datasets
colnames(allevents)[9] <- "count_viol"
str(allevents)








#####################################################################
#                                                                   # 
# train a model using :                                             #
#                                                                   #
#          1. freq (number of bligthed location per building)       #
#          2. Average judgmentamt  per building                     #
#          3. Number of 311 calls  per building                     #
#          4. Number of crimes     per building                     #
#          5. Number of violations per building                     #
#                                                                   # 
#####################################################################
# Here, the number of events for location outside any "building" (cluster of blighted location),
# only count for itself. The freq has to be valued accordingly.

# allevents[which(allevents$cluster_id == 0 & allevents$type != "detdem"),]$count_311   <- 1
# allevents[which(allevents$cluster_id == 0 & allevents$type != "detdem"),]$count_crime <- 1
# allevents[which(allevents$cluster_id == 0 & allevents$type != "detdem"),]$count_viol  <- 1

allevents[which(allevents$cluster_id == 0 & allevents$type == "det311"),]$count_311   <- 1
allevents[which(allevents$cluster_id == 0 & allevents$type == "detcrime"),]$count_crime <- 1
allevents[which(allevents$cluster_id == 0 & allevents$type == "detviol"),]$count_viol  <- 1


# allevents[which(allevents$cluster_id == 0),]$count_311   <- 1
# allevents[which(allevents$cluster_id == 0),]$count_crime <- 1
# allevents[which(allevents$cluster_id == 0),]$count_viol  <- 1

allevents[which(allevents$cluster_id == 0 & allevents$type != "detdem"),]$freq  <- 0

allevents$label <- ""
allevents[which(allevents$cluster_id != 0 | allevents$type == "detdem"),]$label <- "blight"
allevents[which(allevents$cluster_id == 0 & allevents$type != "detdem"),]$label <- "not_blight"

# CreateDataPartition preserves the proportion of the outcome variables.
# We bootstrap a sample for the negative outcome the same as the positive 
# to follow the guidelines.

# Sample return a vector of indices
sam <- allevents[which(allevents$label == "not_blight"),][sample(nrow(allevents[which(allevents$label == "blight"),]), nrow(allevents[which(allevents$label == "blight"),])),]
nrow(sam)

sampled_events <- rbind(
    allevents[which(allevents$label == "blight"),],
    sam
) 

trainIndex <- createDataPartition(sampled_events$label, p = .5,
                                  list = FALSE,
                                  times = 1)

eventstrain <- sampled_events[trainIndex,]
eventstest  <- sampled_events[-trainIndex,]

## 5-fold Cross Validation
fitControl <- trainControl(
    method =  "repeatedcv",
    number = 5,
    repeats = 5)

# Including freq will lead to a perfect model.
eventstrain$label <- factor(eventstrain$label)
glmfit1 <- train(label ~ 
                      freq,
                     # + avg_judg
                     # + count_viol
                     # + count_crime
                     # + count_viol,
                 data = eventstrain,
                 method = "bayesglm",
                 trControl = fitControl,
                 family = "quasibinomial"
                 # ,control = list(maxit = x.5000)
)
glmfit1  
summary(glmfit1)

# glmfit1 <- train(label ~ freq + avg_judg + count_311,
#                   # + count_crime + count_viol zzz
#                   data = eventstrain,
#                   method = "glm1",
#                   trControl = fitControl,
#                   family = "binomial")
# )

# glmfit1 <- train(label ~ avg_judg +  count_311 + count_crime + count_viol,
#                  # +  count_311 + count_crime + count_viol,
#                  data = eventstrain,
#                  method = "glmnet",
#                  trControl = fitControl,
#                  family = "binomial"
# )

# glmfit1  
# summary(glmfit1)






#####################################################################
#                                                                   # 
# Predicting on test set                                            #
#                                                                   # 
#####################################################################
eventstest1 <- eventstest
eventstest1$label <- NULL

predglm <- predict(glmfit1, newdata=eventstest1)
confusionMatrix(predglm, eventstest$label)



eventsneg <- eventstest[which(events$cluster_id == "!ahu"),]
eventsneg[1:10,]
predglm <- predict(glmfit1, newdata=eventsneg)
confusionMatrix(predglm, eventsneg$label)









# Binding datasets
detdem   <- readRDS("detdem_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")
detviol  <- readRDS("detviol_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")
detcrime <- readRDS("detcrime_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")
det311   <- readRDS("det311_geocoded_clustered_3_date_nbuild_f_recomputed_300m_nodup.rds")

# allevents <- rbind(
#     data.frame(type = "detdem", 
#                lat = detdem$lat, 
#                lon = detdem$lon, 
#                cluster_id = detdem$cluster_id, 
#                freq = detdem$freq,
#                label = "blight"),
#     data.frame(type = "detviol", 
#                lat = detviol$lat, 
#                lon = detviol$lon, 
#                cluster_id = detviol$cluster_id, 
#                freq = detviol$freq,
#                label = "not_blight"),
#     data.frame(type = "detcrime", 
#                lat = detcrime$lat, 
#                lon = detcrime$lon, 
#                cluster_id = detcrime$cluster_id, 
#                freq = detcrime$freq,
#                label = "not_blight"),
#     data.frame(type = "det311", 
#                lat = det311$lat, 
#                lon = det311$lon, 
#                cluster_id = det311$cluster_id, 
#                freq = det311$freq,
#                label = "not_blight")
# )



# Come cazzo fanno ad avere una accuratezza del 50 % ?????

# library("sp")
# library("rgdal")
# 
# sp_poly <- SpatialPolygons(list(Polygons(list(Polygon(coords)), ID=1)))
# # set coordinate reference system with SpatialPolygons(..., proj4string=CRS(...))
# # e.g. CRS("+proj=longlat +datum=WGS84")
# sp_poly_df <- SpatialPolygonsDataFrame(sp_poly, data=data.frame(ID=1))
# writeOGR(sp_poly_df, "chull", layer="chull", driver="ESRI Shapefile") # Save shapefile
# 
# # Read shapefile and convert to be plotted on Google map.
# detdemcl <- readOGR(".","nhood_2010")
# 
# We named the shapefile "Neighborhoods" (by typing the name of to the left of <-). 
# The first set of quotations in the command is looking for the location of the data. 
# We already set the working directory to C: so the dot is telling R "slow your roll; you don't need to look any further".
# The second set of quotations in the command is looking for the name of the layer, which in this case is "nhood_2010".
# 
# Now we need to prepare our object so that it may be portrayed on a map. R doesn't know what to do with it in its current form. A few lines of code will transform this caterpillar into a beautiful, map-able butterfly. First, run:
# 
# Neighborhoods <- spTransform(Neighborhoods, CRS("+proj=longlat +datum=WGS84"))
# 
