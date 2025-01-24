library(shiny)
library(shinyWidgets)
library(simstandard)
library(tidyverse)
library(lavaan)
library(lavaanPlot)
library(semPlot)
library(ggnormalviolin)
library(ggtext)
library(ragg)

conditional_covariance <- function(x, sigma, mu = 0) {
  if (!("matrix" %in% class(sigma))) stop("sigma must be a matrix.")
  if (is.null(names(x))) stop("x must be a named vector.")
  if (is.null(colnames(sigma))) stop("sigma must have column names.")
  if (is.null(rownames(sigma))) stop("sigma must have row names.")
  if (!all(rownames(sigma) == colnames(sigma))) stop("The row and column names for sigma must be identical.")
  if (!isSymmetric(sigma)) stop("sigma must be a symmetric square matrix.")
  
  v_names <- colnames(sigma)
  x_names <- names(x)
  y_names <- setdiff(v_names, x_names)
  x_missing <- x_names[is.na(x)]
  x_names <- setdiff(x_names, x_missing)
  
  if (length(y_names) == 0) stop("There are no variables in sigma that are not in x.")
  
  if (length(setdiff(x_names, v_names)) > 0) stop(paste0("The following variables in x are not in sigma: ", setdiff(x_names, v_names)))
  
  if (length(mu) == 1) {
    mu = rep(mu, length(v_names))
    names(mu) <- v_names
  } else if (is.null(names(mu))) {
    if (ncol(sigma) != length(mu)) stop("mu and the columns of sigma are of different length.")
    names(mu) <- v_names
  } else if (!setequal(v_names, names(mu))) {
    stop("The names in mu and the column names of sigma are not the same.")
  } else if (is.null(names(mu))) {
    names(mu) <- x_names
  }
  
  
  sigma_x <- sigma[x_names, x_names]
  if (!all(eigen(sigma_x)$values > 0)) stop("The covariance matrix of the predictor variables is not positive definite.")
  invsigma_x <- solve(sigma_x)
  
  mu_y <- mu[y_names]
  mu_x <- mu[x_names]
  sigma_y <- sigma[y_names, y_names]
  sigma_xy <- sigma[x_names, y_names]
  sigma_yx <- sigma[y_names, x_names]
  mu_y.x <- mu_y + (sigma_yx %*% invsigma_x %*% (x - mu_x))[,1, drop = TRUE]
  
  sigma_y.x <- sigma_y - sigma_yx %*% invsigma_x %*% sigma_xy
  
  l <- list(mu_conditional = mu_y.x,
            sigma_conditional = sigma_y.x,
            descriptives_conditional = data.frame(
              construct = names(mu_y.x),
              mu_conditional = mu_y.x,
              sigma_conditional = sqrt(diag(sigma_y.x, names = TRUE))),
            x = x,
            sigma = sigma,
            mu = mu)
  l
}


prob_label <- function(p,
                       accuracy = 0.01,
                       digits = NULL,
                       max_digits = NULL,
                       remove_leading_zero = TRUE,
                       round_zero_one = TRUE) {
  if (is.null(digits)) {
    l <- scales::number(p, accuracy = accuracy)
  } else {
    sig_digits <- abs(ceiling(log10(p + p / 1000000000)) - digits)
    pgt99 <- p > 0.99
    sig_digits[pgt99] <- abs(ceiling(log10(1 - p[pgt99])) - digits + 1)
    sig_digits[ceiling(log10(p)) == log10(p) & (-log10(p) >= digits)] <- sig_digits[ceiling(log10(p)) == log10(p) & (-log10(p) >= digits)] - 1
    sig_digits[is.infinite(sig_digits)] <- 0
    l <- purrr::map2_chr(p,
                         sig_digits,
                         formatC,
                         format = "f",
                         flag = "#")
    
  }
  if (remove_leading_zero) l <- sub("^-0","-", sub("^0","", l))
  
  if (round_zero_one) {
    l[p == 0] <- "0"
    l[p == 1] <- "1"
    l[p == -1] <- "-1"
  }
  
  if (!is.null(max_digits)) {
    if (round_zero_one) {
      l[round(p, digits = max_digits) == 0] <- "0"
      l[round(p, digits = max_digits) == 1] <- "1"
      l[round(p, digits = max_digits) == -1] <- "-1"
    } else {
      l[round(p, digits = max_digits) == 0] <- paste0(".", paste0(rep("0", max_digits), collapse = ""))
      l[round(p, digits = max_digits) == 1] <- paste0("1.", paste0(rep("0", max_digits), collapse = ""))
      l[round(p, digits = max_digits) == -1] <- paste0("-1.", paste0(rep("0", max_digits), collapse = ""))
    }
  }
  
  l <- sub(pattern = "-", replacement = "−", x = l)
  Encoding(l) <- "UTF-8"
  
  dim(l) <- dim(p)
  l
}

ggtext_size <- function(base_size, ratio = 0.8) {
  ratio * base_size / 2.845276
}

# Options
options(shiny.usecairo = T, # use Cairo device for better antialiasing
        scipen = 999 # Do not use scientific notation
)


sliderInput <- function (inputId, label, min, max, value, step = NULL, round = FALSE, 
          ticks = TRUE, animate = FALSE, width = NULL, sep = ",", 
          pre = NULL, post = NULL, timeFormat = NULL, timezone = NULL, 
          dragRange = TRUE) 
{
  shiny:::validate_slider_value(min, max, value, "sliderInput")
  dataType <- shiny:::getSliderType(min, max, value)
  if (is.null(timeFormat)) {
    timeFormat <- switch(dataType, date = "%F", datetime = "%F %T", 
                         number = NULL)
  }
  value <- restoreInput(id = inputId, default = value)
  if (is.character(value)) {
    if (dataType == "date") {
      value <- as.Date(value, format = "%Y-%m-%d")
    }
    else if (dataType == "datetime") {
      value <- as.POSIXct(value, format = "%Y-%m-%dT%H:%M:%SZ", 
                          tz = "UTC")
    }
  }
  step <- shiny:::findStepSize(min, max, step)
  if (dataType %in% c("date", "datetime")) {
    to_ms <- function(x) 1000 * as.numeric(as.POSIXct(x))
    step <- to_ms(max) - to_ms(max - step)
    min <- to_ms(min)
    max <- to_ms(max)
    value <- to_ms(value)
  }
  range <- max - min
  if (ticks) {
    n_steps <- range/step
    scale_factor <- 10
    n_ticks <- 12
  }
  else {
    n_ticks <- NULL
  }
  sliderProps <- shiny:::dropNulls(list(class = "js-range-slider", 
                                id = inputId, `data-skin` = "shiny", `data-type` = if (length(value) > 
                                                                                       1) "double", `data-min` = shiny:::formatNoSci(min), `data-max` = shiny:::formatNoSci(max), 
                                `data-from` = shiny:::formatNoSci(value[1]), `data-to` = if (length(value) > 
                                                                                     1) shiny:::formatNoSci(value[2]), `data-step` = shiny:::formatNoSci(step), 
                                `data-grid` = ticks, `data-grid-num` = n_ticks, `data-grid-snap` = FALSE, 
                                `data-prettify-separator` = sep, `data-prettify-enabled` = (sep != 
                                                                                              ""), `data-prefix` = pre, `data-postfix` = post, 
                                `data-keyboard` = TRUE, `data-drag-interval` = if (length(value) > 
                                                                                   1) dragRange, `data-data-type` = dataType, `data-time-format` = timeFormat, 
                                `data-timezone` = timezone))
  sliderProps <- lapply(sliderProps, function(x) {
    if (identical(x, TRUE)) 
      "true"
    else if (identical(x, FALSE)) 
      "false"
    else x
  })
  sliderTag <- div(class = "form-group shiny-input-container", 
                   style = htmltools::css(width = htmltools:::validateCssUnit(width)), shiny:::shinyInputLabel(inputId, 
                                                                                label), do.call(tags$input, sliderProps))
  if (identical(animate, TRUE)) 
    animate <- animationOptions()
  if (!is.null(animate) && !identical(animate, FALSE)) {
    if (is.null(animate$playButton)) 
      animate$playButton <- icon("play", lib = "glyphicon")
    if (is.null(animate$pauseButton)) 
      animate$pauseButton <- icon("pause", lib = "glyphicon")
    sliderTag <- tagAppendChild(sliderTag, tags$div(class = "slider-animate-container", 
                                                    tags$a(href = "#", class = "slider-animate-button", 
                                                           `data-target-id` = inputId, `data-interval` = animate$interval, 
                                                           `data-loop` = animate$loop, span(class = "play", 
                                                                                            animate$playButton), span(class = "pause", 
                                                                                                                      animate$pauseButton))))
  }
  htmltools:::attachDependencies(sliderTag, shiny:::ionRangeSliderDependency())
}

# UI ----
ui <- fluidPage(
  tags$head(
    tags$style(
      type = "text/css",
      '.irs-from, .irs-to, .irs-min, .irs-max {
            visibility: hidden !important;} .irs-single {font-size:14px !important;} '
    )
  ),
  
  # Application title ----
  titlePanel("Conditional Distributions"),
  
  # Sidebar ----
  sidebarLayout(sidebarPanel(uiOutput("observed")),
                
                # Main ----
                mainPanel(
                  tabsetPanel(
                    id = 'main',
                    tabPanel(
                      "Specify Model",
                      ## lavaanmodel ----
                      textAreaInput(
                        inputId = "lavaanmodel",
                        label = "Standardized Coefficient Model (lavaan syntax)",
                        value = paste0(
                          c(
                            "# Latent Variables",
                            "A =~ .86 * a1 + .90 * a2 + .92 * a3",
                            "B =~ .94 * b1 + .88 * b2",
                            "C =~ .86 * c1 + .90 * c2 + .92 * c3",
                            "g =~ .9 * A + .7 * B + .8 * C",
                            "",
                            "# Regressions",
                            "",
                            "# Correlations",
                            ""
                          ),
                          collapse = "\n"
                        ),
                        height = "500px",
                        width = "100%"
                      ),
                      
                    ),
                    ## Modelplot ----
                    tabPanel("Path",
                             plotOutput("modelplot")),
                    tabPanel(
                      "Model-implied Correlations",
                      DT::DTOutput("implied-correlation")
                    ),
                    ## Estimates Tables ----
                    tabPanel(
                      "Observed Variables",
                      tableOutput("SS"),
                      tags$h3("Conditional Estimates"),
                      tableOutput("latent")
                    ),
                    tabPanel(
                      "Plot",
                      plotOutput("violinplot", height = "600px"),
                      shiny::inputPanel(
                        cellArgs = list(
                          style = "
          min-width: 200px;
          width: auto;
          height: auto;
          padding: 2px 5px;
          margin: 2px 10px;
        "
                        ),
        awesomeCheckboxGroup(
          inputId = "chkplot",
          label = "Display",
          choices = c("Latent", "Disturbance", "Error"),
          inline = TRUE,
          selected = c("Latent", "Disturbance")
        ),
        uiOutput("chkcolor"),
        numericInput("samplesize", "Cases", value = 500,min = 1),
        width = "100%"
                      )
                    )
                  )
                ))
)

# Server ----
server <- function(input, output) {
  # fit ----
  fit <- reactive({
    m <- input$lavaanmodel
    ssm <- sim_standardized_matrices(m)
    lavtab <- lavaan::lavaanify(m)
    latents <- lavtab %>%
      filter(op == "=~") %>%
      select(lhs, rhs) %>%
      filter(rhs %in% ssm$v_names$v_observed_indicator) %>%
      group_by(lhs) %>%
      mutate(k = n()) |>
      ungroup() |>
      arrange(rhs,k) |>
      group_by(rhs) |>
      mutate(id = row_number()) |>
      filter(id == 1) |>
      select(-k, -id) |>
      group_by(lhs) |> 
      nest()
    ssm$latents <- latents
    ssm
  })
  
  
  # modelplot ----
  output$modelplot <- renderPlot({
    semPlot::semPaths(
      lavaanify(fit()$lavaan_models$model_with_variances),
      what = "est",
      edge.color = "gray",
      edge.width = .25,
      curveAdjacent = "<->",
      layout = "tree3",
      unCol = "#070b8c",
      nCharNodes = 0,
      whatLabels = "est",
      exoVar = FALSE,
      residuals = FALSE,
      fixedStyle = 1
    )
    
    
  })
  
  
  # correlations ----
  output$`implied-correlation` <- DT::renderDT({
    get_model_implied_correlations(
      fit(),
      observed = T,
      latent = T,
      errors = T,
      factor_scores = F
    ) %>%
      as.data.frame() %>%
      mutate(across(.fns = prob_label, accuracy = .0001)) %>%
      tibble::rownames_to_column("Variable") %>% 
      DT::datatable(., filter = "none",options = list(ordering = F, dom = 't', pageLength = 100)) %>% 
      DT::formatStyle(columns = -1, `text-align` = "center")
    
  }
  )
  
  
  # observed ----
  output$observed <- renderUI({
    pmap(fit()$latents, \(lhs, data) {
      shiny::fluidRow(h3(paste0(lhs, " Indicators:")),
                      map(
                        data$rhs,
                        \(x) sliderInput(
                          inputId = paste0("ob_", x),
                          label = NULL,
                          min = 40,
                          max = 160,
                          value = 100,
                          pre = paste0(x, " = ")
                        )
                      ))
    })
  })
  
  # x scores ----
  x <- reactive({
    v_observed <- get_model_names(fit())$v_observed
    
    x_SS <- integer(length(v_observed))
    names(x_SS) <- v_observed
    
    for (v in v_observed) {
      x_SS[v] <- input[[paste0("ob_", v)]]
    }
    x_SS
  })
  
  # SS ----
  output$SS <- renderTable(data.frame(Variable = names(x()),
                                      SS = x()), striped = T)
  
  # cond_cov ----
  cond_cov <-
    reactive(
      conditional_covariance(
        x(),
        get_model_implied_correlations(
          fit(),
          observed = T,
          latent = T,
          errors = T
        ) * 225,
        mu = 100
      )
    )
  
  # latent table ----
  
  output$latent <-
    renderTable((cond_cov()$descriptives_conditional) %>% rename(
      Variable = construct,
      Estimate = mu_conditional,
      `Std. Error` = sigma_conditional
    ), striped = T
    )
  
  # cnkcolor ----
  output$chkcolor <- renderUI({
    v_names <-
      c(fit()$v_names$v_latent,
        fit()$v_names$v_disturbance,
        fit()$v_names$v_error)
    shiny::selectInput(
      "plotcolor",
      label = "Color by",
      choices = v_names,
      selected = v_names[1],
      multiple = F,
      selectize = F
    )
  })
  # violin plot ----
  output$violinplot <- renderPlot({
    vtype_color <- viridis::viridis(n = 3,
                                    begin = .25,
                                    end = .85) %>%
      `names<-`(c("Latent", "Disturbance", "Error"))
    
    vv <- input$plotcolor
    
    mylabels <- function(x) {
      intcolor <- 1 + str_starts(x, "d_") * 1 + str_starts(x, "e_") * 2
      ifelse(
        str_detect(x, "_"),
        paste0(
          "<span style='color:",
          vtype_color[intcolor],
          ";'>",
          str_replace(x, "_", "<sub>"),
          "</sub></span>"
        ),
        paste0(
          "<span style='color:",
          vtype_color[intcolor],
          ";'>",
          x,
          "</span>"
        )
      )
    }
    
    if (!is.null(vv)) {
      d <-
        (
          mvtnorm::rmvnorm(
            n = input$samplesize,
            mean = cond_cov()$mu_conditional,
            sigma = cond_cov()$sigma_conditional
          )
        ) %>%
        as_tibble() %>%
        arrange(!!sym(vv)) %>%
        mutate(id = fct_inorder(factor(row_number())),
               id2 = fct_shuffle(id)) %>%
        pivot_longer(
          cols = c(-id,-id2),
          names_to = "construct",
          values_to = "score"
        ) %>%
        mutate(vtype = ifelse(
          str_starts(construct, "d_"),
          "Disturbance",
          ifelse(str_starts(construct, "e_"), "Error", "Latent")
        ) %>% factor(levels = c("Latent", "Disturbance", "Error")))
      
      d_cond <- cond_cov()$descriptives_conditional %>%
        mutate(vtype = ifelse(
          str_starts(construct, "d_"),
          "Disturbance",
          ifelse(str_starts(construct, "e_"),
                 "Error",
                 "Latent")
        ) %>%
          factor(levels = c("Latent", "Disturbance", "Error"))) %>%
        mutate(construct = fct_inorder(construct))
      
      d <- filter(d, vtype %in% input$chkplot)
      d_cond <- filter(d_cond, vtype %in% input$chkplot)
      
      if (nrow(d_cond) > 0) {
        d_cond %>%
          ggplot(aes(construct, mu_conditional)) +
          annotate(
            geom = "tile",
            x = nrow(d_cond) / 2  + .5,
            y = 100,
            width = nrow(d_cond) + .5,
            height = 140,
            alpha = .4,
            fill = "black"
          ) +
          annotate(
            geom = "tile",
            x = nrow(d_cond) / 2 + .5,
            y = 100,
            width =  nrow(d_cond) + .5,
            height = 90,
            alpha = .5,
            fill = "black"
          ) +
          annotate(
            geom = "tile",
            x = nrow(d_cond) / 2 + .5,
            y = 100,
            width =  nrow(d_cond) + .5,
            height = 60,
            alpha = .5,
            fill = "black"
          ) +
          annotate(
            geom = "tile",
            x = nrow(d_cond) / 2 + .5,
            y = 100,
            width =  nrow(d_cond) + .5,
            height = 30,
            alpha = .8,
            fill = "black"
          ) +
          geom_vline(
            xintercept = seq(1, 5),
            color = "gray40",
            size = .25,
            alpha = .4
          ) +
          geom_hline(
            yintercept = seq(45, 160, 15),
            color = "gray40",
            size = .25,
            alpha = .4
          ) +
          geom_hline(
            yintercept = seq(50, 160, 15),
            color = "gray40",
            size = .25,
            alpha = .4
          ) +
          geom_hline(
            yintercept = seq(40, 160, 15),
            color = "gray40",
            size = .25,
            alpha = .4
          ) +
          geom_hline(
            yintercept = 100,
            color = "gray60",
            size = .25,
            alpha = .4
          ) +
          geom_normalviolin(
            aes(
              mu = mu_conditional,
              sigma = sigma_conditional,
              fill = vtype
            ),
            alpha = .85,
            p_tail = .05
          ) +
          geom_path(
            data = d,
            aes(
              y = score,
              group = id2,
              color = id
            ),
            size = .1,
            alpha = .4
          ) +
          scale_x_discrete(NULL, labels = mylabels) +
          geom_linerange(
            aes(
              ymin = mu_conditional - sigma_conditional,
              ymax = mu_conditional + sigma_conditional
            )
          ) +
          geom_label(
            aes(
              label = round(mu_conditional, 0)
            ),
            color = vtype_color[d_cond$vtype],
            fill = "black",
            family = "Roboto Condensed",
            size = ggtext_size(20), label.size = 0, label.r = unit(.5, "lines")
          ) +
          scale_y_continuous(
            NULL,
            breaks = seq(40, 160, 15),
            minor_breaks = seq(40, 160, 5),
            expand = expansion()
          ) +
          theme_minimal(
            base_size = 20,
            base_line_size = .5,
            base_family = "Roboto Condensed"
          ) +
          theme(
            legend.position = "none",
            axis.text.y = element_text(color = "gray50"),
            axis.text.x = element_markdown(face = "italic"),
            panel.grid.major = element_blank(),
            panel.grid.minor = element_blank(),
            plot.background = element_rect(fill = "black"),
            panel.background = element_rect(fill = "white"),
            title = element_text(color = "gray70")
          ) +
          coord_cartesian(ylim = c(40, 160)) +
          scico::scale_color_scico_d(palette = "roma") +
          # scale_color_viridis_d(end = .9) +
          scale_fill_manual(values = vtype_color) + 
          ggtitle("Conditional Distributions, Given Observed Scores")
      }
      
    }
    
  })
  
  updateTabsetPanel(inputId = "main", selected = "Plot")
  
  
  
  
  
  
}

# Run the application ----
shinyApp(ui = ui, server = server)
